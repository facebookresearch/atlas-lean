/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.ImageToKernel
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Boundaries and cycles of a nonnegative chain complex

Let C be abelian and L a chain complex indexed by ℕ. Its outgoing image Bⱼ⁽out⁾=im(dFrom_L(j))
gives the two canonical short exact sequences 0 → Bⱼ₊₁⁽out⁾ → Zⱼ(L) → Hⱼ(L) → 0 and 0 → Zⱼ(L) →
Lⱼ → Bⱼ⁽out⁾ → 0. The degree-zero outgoing image is zero. Every chain map acts on these images,
cycles, terms and homology objects and gives commuting maps of both short exact sequences.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits ZeroObject

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- For every natural number j, the down-ℕ chain-complex shape allows a differential from degree j+1
to degree j: its relation satisfies Rel(j+1,j). -/
theorem chainComplexSuccRel (j : ℕ) :
    (ComplexShape.down ℕ).Rel (j + 1) j :=
  rfl

/-- Let C be abelian and L a natural-number-indexed chain complex. Write Bⱼ⁽out⁾=im(dFrom_L(j)) for
the image of its outgoing differential, Zⱼ(L) for cycles and Hⱼ(L) for homology. For j ∈ ℕ,
boundaryFrom(L,j) is the outgoing image Bⱼ⁽out⁾. In positive degree j+1 it is the incoming
boundary of degree j; in degree zero it is zero. -/
noncomputable abbrev boundaryFrom (L : ChainComplex C ℕ) (j : ℕ) : C :=
  image (L.dFrom j)

/-- Let C be abelian and L a natural-number-indexed chain complex. Write Bⱼ⁽out⁾=im(dFrom_L(j)) for
the image of its outgoing differential, Zⱼ(L) for cycles and Hⱼ(L) for homology. For every j ∈ ℕ
there is a canonical isomorphism Bⱼ₊₁⁽out⁾ ≅ im(d_L^{j+1,j}), retaining the original
differential into degree j. -/
noncomputable def boundaryFromSuccToCanonicalImageIso
    (L : ChainComplex C ℕ) (j : ℕ) :
    L.boundaryFrom (j + 1) ≅ image (L.d (j + 1) j) :=
  image.eqToIso (L.dFrom_eq (chainComplexSuccRel j)) ≪≫
    (image.compIso (L.d (j + 1) j)
      (L.xNextIso (chainComplexSuccRel j)).inv).symm

@[reassoc (attr := simp)]
theorem boundaryFromSuccToCanonicalImageIso_hom_ι
    (L : ChainComplex C ℕ) (j : ℕ) :
    (L.boundaryFromSuccToCanonicalImageIso j).hom ≫
        image.ι (L.d (j + 1) j) =
      image.ι (L.dFrom (j + 1)) ≫
        (L.xNextIso (chainComplexSuccRel j)).hom := by
  change
    (image.eqToIso (L.dFrom_eq (chainComplexSuccRel j)) ≪≫
      (image.compIso (L.d (j + 1) j)
        (L.xNextIso (chainComplexSuccRel j)).inv).symm).hom ≫
        image.ι (L.d (j + 1) j) = _
  simp only [Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc]
  rw [image.compIso_inv_comp_image_ι]
  rw [← Category.assoc,
    ← image.eq_fac (L.dFrom_eq (chainComplexSuccRel j))]
  exact congrArg (image.ι (L.dFrom (j + 1)) ≫ ·)
    (IsIso.Iso.inv_inv (L.xNextIso (chainComplexSuccRel j)))

/-- Let C be abelian and L a natural-number-indexed chain complex. Write Bⱼ⁽out⁾=im(dFrom_L(j)) for
the image of its outgoing differential, Zⱼ(L) for cycles and Hⱼ(L) for homology. The boundary
image sourced in degree j+1 is canonically isomorphic to im(dTo_L(j)), the incoming differential
image used to compute Hⱼ(L). -/
noncomputable def boundaryFromSuccIso (L : ChainComplex C ℕ) (j : ℕ) :
    L.boundaryFrom (j + 1) ≅ image (L.dTo j) := by
  let eTo : image (L.dTo j) ≅ image (L.d (j + 1) j) :=
    image.eqToIso (L.dTo_eq (chainComplexSuccRel j)) ≪≫
      asIso (image.preComp (L.xPrevIso (chainComplexSuccRel j)).hom
        (L.d (j + 1) j))
  exact L.boundaryFromSuccToCanonicalImageIso j ≪≫ eTo.symm

/-- Let C be abelian and L a natural-number-indexed chain complex. Write Bⱼ⁽out⁾=im(dFrom_L(j)) for
the image of its outgoing differential, Zⱼ(L) for cycles and Hⱼ(L) for homology. The outgoing
boundary in degree zero is a zero object: B₀⁽out⁾ ≅ 0, since a nonnegative chain complex has no
differential out of degree zero. -/
noncomputable def boundaryFromZeroIso (L : ChainComplex C ℕ) :
    L.boundaryFrom 0 ≅ 0 :=
  imageZero' (L.dFrom_eq_zero (i := 0) (by simp))

/-- Let C be abelian, f : L → L′ a map of ℕ-indexed chain complexes, and j ∈ ℕ. The commuting
differential square induces a morphism Bⱼ⁽out⁾(L) → Bⱼ⁽out⁾(L′) of outgoing images. -/
noncomputable def boundaryFromMap {L L' : ChainComplex C ℕ}
    (f : L ⟶ L') (j : ℕ) :
    L.boundaryFrom j ⟶ L'.boundaryFrom j :=
  image.map (f.sqFrom j)

@[reassoc (attr := simp)]
theorem boundaryFromMap_ι {L L' : ChainComplex C ℕ}
    (f : L ⟶ L') (j : ℕ) :
    boundaryFromMap f j ≫ image.ι (L'.dFrom j) =
      image.ι (L.dFrom j) ≫ f.next j := by
  exact image.map_ι (f.sqFrom j)

@[reassoc (attr := simp)]
theorem factor_boundaryFromMap {L L' : ChainComplex C ℕ}
    (f : L ⟶ L') (j : ℕ) :
    factorThruImage (L.dFrom j) ≫ boundaryFromMap f j =
      f.f j ≫ factorThruImage (L'.dFrom j) := by
  exact image.factor_map (f.sqFrom j)

@[simp]
theorem boundaryFromMap_id (L : ChainComplex C ℕ) (j : ℕ) :
    boundaryFromMap (𝟙 L) j = 𝟙 _ := by
  change image.map (Hom.sqFrom (𝟙 L) j) = 𝟙 _
  rw [Hom.sqFrom_id, image.map_id]

@[reassoc, simp]
theorem boundaryFromMap_comp {L L' L'' : ChainComplex C ℕ}
    (f : L ⟶ L') (g : L' ⟶ L'') (j : ℕ) :
    boundaryFromMap (f ≫ g) j =
      boundaryFromMap f j ≫ boundaryFromMap g j := by
  change image.map ((f ≫ g).sqFrom j) =
    image.map (f.sqFrom j) ≫ image.map (g.sqFrom j)
  rw [Hom.sqFrom_comp, image.map_comp]

/-- Let C be abelian and L a natural-number-indexed chain complex. Write Bⱼ⁽out⁾=im(dFrom_L(j)) for
the image of its outgoing differential, Zⱼ(L) for cycles and Hⱼ(L) for homology. For each j ∈ ℕ,
the kernel of the actual outgoing differential dFrom_L(j) is canonically isomorphic to Zⱼ(L). -/
noncomputable def kernelDFromIsoCycles (L : ChainComplex C ℕ) (j : ℕ) :
    kernel (L.dFrom j) ≅ L.cycles j :=
  IsLimit.conePointUniqueUpToIso (kernelIsKernel (L.dFrom j))
    (L.cyclesIsKernel j _ rfl)

@[reassoc (attr := simp)]
theorem kernelDFromIsoCycles_hom_iCycles
    (L : ChainComplex C ℕ) (j : ℕ) :
    (L.kernelDFromIsoCycles j).hom ≫ L.iCycles j =
      kernel.ι (L.dFrom j) :=
  IsLimit.conePointUniqueUpToIso_hom_comp
    (kernelIsKernel (L.dFrom j)) (L.cyclesIsKernel j _ rfl)
      WalkingParallelPair.zero

/-- Let C be abelian and L a natural-number-indexed chain complex. Write Bⱼ⁽out⁾=im(dFrom_L(j)) for
the image of its outgoing differential, Zⱼ(L) for cycles and Hⱼ(L) for homology. The incoming
boundary Bⱼ₊₁⁽out⁾ maps canonically into Zⱼ(L), with composite to Lⱼ equal to its
differential-image inclusion. -/
noncomputable def boundaryToCycles (L : ChainComplex C ℕ) (j : ℕ) :
    L.boundaryFrom (j + 1) ⟶ L.cycles j :=
  (L.boundaryFromSuccToCanonicalImageIso j).hom ≫
    imageToKernel' (L.d (j + 1) j) (L.dFrom j)
      (L.d_comp_d (j + 1) j _) ≫
    (L.kernelDFromIsoCycles j).hom

@[reassoc (attr := simp)]
theorem boundaryToCycles_i (L : ChainComplex C ℕ) (j : ℕ) :
    L.boundaryToCycles j ≫ L.iCycles j =
      image.ι (L.dFrom (j + 1)) ≫
        (L.xNextIso (chainComplexSuccRel j)).hom := by
  calc
    L.boundaryToCycles j ≫ L.iCycles j =
        (L.boundaryFromSuccToCanonicalImageIso j).hom ≫
          imageToKernel' (L.d (j + 1) j) (L.dFrom j)
            (L.d_comp_d (j + 1) j _) ≫
          ((L.kernelDFromIsoCycles j).hom ≫ L.iCycles j) := by
              change
                ((L.boundaryFromSuccToCanonicalImageIso j).hom ≫
                  (imageToKernel' (L.d (j + 1) j) (L.dFrom j)
                    (L.d_comp_d (j + 1) j _) ≫
                      (L.kernelDFromIsoCycles j).hom)) ≫ L.iCycles j = _
              rw [Category.assoc, Category.assoc]
    _ = (L.boundaryFromSuccToCanonicalImageIso j).hom ≫
          imageToKernel' (L.d (j + 1) j) (L.dFrom j)
            (L.d_comp_d (j + 1) j _) ≫ kernel.ι (L.dFrom j) := by
              rw [kernelDFromIsoCycles_hom_iCycles]
    _ = (L.boundaryFromSuccToCanonicalImageIso j).hom ≫
          image.ι (L.d (j + 1) j) := by
              rw [imageToKernel', kernel.lift_ι]
    _ = image.ι (L.dFrom (j + 1)) ≫
          (L.xNextIso (chainComplexSuccRel j)).hom :=
      L.boundaryFromSuccToCanonicalImageIso_hom_ι j

instance (L : ChainComplex C ℕ) (j : ℕ) :
    Mono (L.boundaryToCycles j) :=
  mono_of_mono_fac (L.boundaryToCycles_i j)

@[reassoc (attr := simp)]
theorem factor_boundaryToCycles (L : ChainComplex C ℕ) (j : ℕ) :
    factorThruImage (L.dFrom (j + 1)) ≫ L.boundaryToCycles j =
      L.toCycles (j + 1) j := by
  apply (cancel_mono (L.iCycles j)).1
  calc
    (factorThruImage (L.dFrom (j + 1)) ≫ L.boundaryToCycles j) ≫
        L.iCycles j =
      factorThruImage (L.dFrom (j + 1)) ≫
        image.ι (L.dFrom (j + 1)) ≫
          (L.xNextIso (chainComplexSuccRel j)).hom := by
            rw [Category.assoc, boundaryToCycles_i]
    _ = L.dFrom (j + 1) ≫
          (L.xNextIso (chainComplexSuccRel j)).hom := by
            rw [image.fac_assoc]
    _ = L.d (j + 1) j :=
      L.dFrom_comp_xNextIso (chainComplexSuccRel j)
    _ = L.toCycles (j + 1) j ≫ L.iCycles j := by
      rw [toCycles_i]

@[reassoc (attr := simp)]
theorem boundaryToCycles_naturality {L L' : ChainComplex C ℕ}
    (f : L ⟶ L') (j : ℕ) :
    boundaryFromMap f (j + 1) ≫ L'.boundaryToCycles j =
      L.boundaryToCycles j ≫ cyclesMap f j := by
  apply (cancel_mono (L'.iCycles j)).1
  calc
    (boundaryFromMap f (j + 1) ≫ L'.boundaryToCycles j) ≫
        L'.iCycles j =
      boundaryFromMap f (j + 1) ≫
        image.ι (L'.dFrom (j + 1)) ≫
          (L'.xNextIso (chainComplexSuccRel j)).hom := by
            rw [Category.assoc, L'.boundaryToCycles_i]
    _ = image.ι (L.dFrom (j + 1)) ≫ f.next (j + 1) ≫
          (L'.xNextIso (chainComplexSuccRel j)).hom := by
            rw [boundaryFromMap_ι_assoc]
    _ = image.ι (L.dFrom (j + 1)) ≫
          (L.xNextIso (chainComplexSuccRel j)).hom ≫ f.f j := by
            rw [f.next_eq (chainComplexSuccRel j)]
            simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = L.boundaryToCycles j ≫ L.iCycles j ≫ f.f j := by
      rw [L.boundaryToCycles_i_assoc]
    _ = (L.boundaryToCycles j ≫ cyclesMap f j) ≫
          L'.iCycles j := by
      rw [Category.assoc, cyclesMap_i]

/-- Let C be abelian and L a natural-number-indexed chain complex. Write Bⱼ⁽out⁾=im(dFrom_L(j)) for
the image of its outgoing differential, Zⱼ(L) for cycles and Hⱼ(L) for homology. The degree-j
short complex is Bⱼ₊₁⁽out⁾ → Zⱼ(L) → Hⱼ(L), using boundary inclusion and the canonical homology
quotient. -/
noncomputable def boundaryCyclesHomologyShortComplex
    (L : ChainComplex C ℕ) (j : ℕ) : ShortComplex C :=
  ShortComplex.mk (L.boundaryToCycles j) (L.homologyπ j) (by
    apply (cancel_epi (factorThruImage (L.dFrom (j + 1)))).1
    calc
      factorThruImage (L.dFrom (j + 1)) ≫
          (L.boundaryToCycles j ≫ L.homologyπ j) =
        (factorThruImage (L.dFrom (j + 1)) ≫
          L.boundaryToCycles j) ≫ L.homologyπ j := by
            rw [Category.assoc]
      _ = L.toCycles (j + 1) j ≫ L.homologyπ j := by
        rw [factor_boundaryToCycles]
      _ = 0 := L.toCycles_comp_homologyπ (j + 1) j
      _ = factorThruImage (L.dFrom (j + 1)) ≫ 0 := by simp)

/-- Let C be abelian and L a natural-number-indexed chain complex. Write Bⱼ⁽out⁾=im(dFrom_L(j)) for
the image of its outgoing differential, Zⱼ(L) for cycles and Hⱼ(L) for homology. The degree-j
short complex is Zⱼ(L) → Lⱼ → Bⱼ⁽out⁾, using the cycle inclusion and factorization of the
outgoing differential onto its image. -/
noncomputable def cyclesTermBoundaryShortComplex
    (L : ChainComplex C ℕ) (j : ℕ) : ShortComplex C :=
  ShortComplex.mk (L.iCycles j) (factorThruImage (L.dFrom j)) (by
    apply (cancel_mono (image.ι (L.dFrom j))).1
    calc
      (L.iCycles j ≫ factorThruImage (L.dFrom j)) ≫
          image.ι (L.dFrom j) =
        L.iCycles j ≫ L.dFrom j := by
          rw [Category.assoc, image.fac]
      _ = 0 := L.iCycles_d j _
      _ = 0 ≫ image.ι (L.dFrom j) := by simp)

/-- Let C be abelian and L a natural-number-indexed chain complex. Write Bⱼ⁽out⁾=im(dFrom_L(j)) for
the image of its outgoing differential, Zⱼ(L) for cycles and Hⱼ(L) for homology. For every j ∈
ℕ, the canonical sequence 0 → Bⱼ₊₁⁽out⁾ → Zⱼ(L) → Hⱼ(L) → 0 is short exact. -/
theorem boundaryCyclesHomologyShortExact
    (L : ChainComplex C ℕ) (j : ℕ) :
    (L.boundaryCyclesHomologyShortComplex j).ShortExact := by
  let S := L.boundaryCyclesHomologyShortComplex j
  let _ : Mono S.f := by
    change Mono (L.boundaryToCycles j)
    infer_instance
  let _ : Epi S.g := by
    change Epi (L.homologyπ j)
    infer_instance
  have hCokernel : IsColimit
      (CokernelCofork.ofπ S.g S.zero) := by
    dsimp only [S, boundaryCyclesHomologyShortComplex]
    let h := L.homologyIsCokernel (j + 1) j (by simp)
    exact isCokernelOfComp
      (factorThruImage (L.dFrom (j + 1)))
      (L.toCycles (j + 1) j) h S.zero
      (L.factor_boundaryToCycles j)
  exact ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_g_is_cokernel S hCokernel)
      inferInstance inferInstance

/-- Let C be abelian and L a natural-number-indexed chain complex. Write Bⱼ⁽out⁾=im(dFrom_L(j)) for
the image of its outgoing differential, Zⱼ(L) for cycles and Hⱼ(L) for homology. For every j ∈
ℕ, the canonical sequence 0 → Zⱼ(L) → Lⱼ → Bⱼ⁽out⁾ → 0 is short exact. -/
theorem cyclesTermBoundaryShortExact
    (L : ChainComplex C ℕ) (j : ℕ) :
    (L.cyclesTermBoundaryShortComplex j).ShortExact := by
  let S := L.cyclesTermBoundaryShortComplex j
  let _ : Mono S.f := by
    change Mono (L.iCycles j)
    infer_instance
  let _ : Epi S.g := by
    change Epi (factorThruImage (L.dFrom j))
    infer_instance
  have hKernel : IsLimit
      (KernelFork.ofι S.f S.zero) := by
    dsimp only [S, cyclesTermBoundaryShortComplex]
    exact isKernelOfComp (image.ι (L.dFrom j)) (L.dFrom j)
      (L.cyclesIsKernel j _ rfl) S.zero (image.fac (L.dFrom j))
  exact ShortComplex.ShortExact.mk'
    (ShortComplex.exact_of_f_is_kernel S hKernel)
      inferInstance inferInstance

/-- Let C be abelian and f : L → L′ a map of nonnegative chain complexes. For each j, the induced
maps on Bⱼ₊₁⁽out⁾, Zⱼ and Hⱼ give a morphism of the two boundary–cycle–homology short exact
sequences. -/
noncomputable def boundaryCyclesHomologyMap
    {L L' : ChainComplex C ℕ} (f : L ⟶ L') (j : ℕ) :
    L.boundaryCyclesHomologyShortComplex j ⟶
      L'.boundaryCyclesHomologyShortComplex j where
  τ₁ := boundaryFromMap f (j + 1)
  τ₂ := cyclesMap f j
  τ₃ := homologyMap f j
  comm₁₂ := boundaryToCycles_naturality f j
  comm₂₃ := (homologyπ_naturality f j).symm

/-- Let C be abelian and f : L → L′ a map of nonnegative chain complexes. For each j, the cycle map
Zⱼ(f), term map fⱼ and outgoing-image map give a morphism of the short exact sequences 0 → Zⱼ →
Lⱼ → Bⱼ⁽out⁾ → 0. -/
noncomputable def cyclesTermBoundaryMap
    {L L' : ChainComplex C ℕ} (f : L ⟶ L') (j : ℕ) :
    L.cyclesTermBoundaryShortComplex j ⟶
      L'.cyclesTermBoundaryShortComplex j where
  τ₁ := cyclesMap f j
  τ₂ := f.f j
  τ₃ := boundaryFromMap f j
  comm₁₂ := cyclesMap_i f j
  comm₂₃ := (factor_boundaryFromMap f j).symm

@[simp]
theorem boundaryCyclesHomologyMap_id
    (L : ChainComplex C ℕ) (j : ℕ) :
    boundaryCyclesHomologyMap (𝟙 L) j = 𝟙 _ := by
  ext <;> simp [boundaryCyclesHomologyMap,
    boundaryCyclesHomologyShortComplex]

@[reassoc, simp]
theorem boundaryCyclesHomologyMap_comp
    {L L' L'' : ChainComplex C ℕ}
    (f : L ⟶ L') (g : L' ⟶ L'') (j : ℕ) :
    boundaryCyclesHomologyMap (f ≫ g) j =
      boundaryCyclesHomologyMap f j ≫ boundaryCyclesHomologyMap g j := by
  ext <;> simp [boundaryCyclesHomologyMap,
    boundaryCyclesHomologyShortComplex, cyclesMap_comp, homologyMap_comp]

@[simp]
theorem cyclesTermBoundaryMap_id
    (L : ChainComplex C ℕ) (j : ℕ) :
    cyclesTermBoundaryMap (𝟙 L) j = 𝟙 _ := by
  ext <;> simp [cyclesTermBoundaryMap, cyclesTermBoundaryShortComplex]

@[reassoc, simp]
theorem cyclesTermBoundaryMap_comp
    {L L' L'' : ChainComplex C ℕ}
    (f : L ⟶ L') (g : L' ⟶ L'') (j : ℕ) :
    cyclesTermBoundaryMap (f ≫ g) j =
      cyclesTermBoundaryMap f j ≫ cyclesTermBoundaryMap g j := by
  ext <;> simp [cyclesTermBoundaryMap, cyclesTermBoundaryShortComplex,
    cyclesMap_comp]

end HomologicalComplex

end
