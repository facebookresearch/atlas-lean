/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.Algebra.Homology.CochainComplex.BoundedAmbientAcyclicTopKernel
public import MathlibExt.CategoryTheory.ExactCategory.KernelOfEpiLift

/-!
# Source cycles of an ambient-acyclic bounded complex

Let F:E → A be an additive fully faithful functor from a preadditive
category to an abelian category. Assume its essential image is closed under
kernels of epimorphisms between image objects. For a bounded complex K
supported in [a,b] with F(K) acyclic, begin at Z_b=K^b and descend by
representing kernels of the preceding quotient maps. This gives source
objects Z_j and maps Z_j → K^j → Z_{j+1} in every integer degree.

The rows map to short exact sequences in A and the source cycles have the
same support bounds. If E is Quillen exact with a zero object and binary
biproducts, and F reflects admissible exactness, these rows are conflations.
Conversely, an additive exact functor carries such source conflations to
an acyclic ambient complex. For an exact embedding with the stated closure
and reflection properties, ambient acyclicity is equivalent to existence
of all-degree admissible cycle data. The four category object and morphism
universes are independent.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

universe uE vE uA vA

open CategoryTheory CategoryTheory.Limits CategoryTheory.ExactCategory
open scoped ZeroObject

namespace CochainComplex.Bounded.AmbientCycles

variable {E : Type uE} [Category.{vE} E] [Preadditive E]
variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable (F : E ⥤ A) [F.Additive]

/-- Let E be preadditive, A abelian and F:E → A additive.
Let K be a bounded integer cochain complex in E. A degree-j cycle datum has an object Z_j and maps
q_in:K^{j−1} → Z_j, ι:Z_j → K^j, with ι∘q_in=d_K^{j−1},
d_K^j∘ι=0, F(q_in) epic, and F(ι) a kernel of F(d_K^j).

The structure of a source-cycle datum at degree j, recording this object, the two factorization maps and the mapped epi/kernel properties. -/
structure CycleData (K : Bounded E) (j : ℤ) where
  /-- Let E be preadditive, A abelian and F:E → A additive.
Let K be a bounded integer cochain complex in E. A degree-j cycle datum has an object Z_j and maps
q_in:K^{j−1} → Z_j, ι:Z_j → K^j, with ι∘q_in=d_K^{j−1},
d_K^j∘ι=0, F(q_in) epic, and F(ι) a kernel of F(d_K^j).

The object Z_j in E representing the ambient cycles in degree j. -/
  Z : E
  /-- Let E be preadditive, A abelian and F:E → A additive.
Let K be a bounded integer cochain complex in E. A degree-j cycle datum has an object Z_j and maps
q_in:K^{j−1} → Z_j, ι:Z_j → K^j, with ι∘q_in=d_K^{j−1},
d_K^j∘ι=0, F(q_in) epic, and F(ι) a kernel of F(d_K^j).

The inclusion ι:Z_j → K^j. -/
  ι : Z ⟶ K.obj.X j
  /-- Let E be preadditive, A abelian and F:E → A additive.
Let K be a bounded integer cochain complex in E. A degree-j cycle datum has an object Z_j and maps
q_in:K^{j−1} → Z_j, ι:Z_j → K^j, with ι∘q_in=d_K^{j−1},
d_K^j∘ι=0, F(q_in) epic, and F(ι) a kernel of F(d_K^j).

The incoming quotient q_in:K^{j−1} → Z_j. -/
  q : K.obj.X (j - 1) ⟶ Z
  /-- Let E be preadditive, A abelian and F:E → A additive.
Let K be a bounded integer cochain complex in E. A degree-j cycle datum has an object Z_j and maps
q_in:K^{j−1} → Z_j, ι:Z_j → K^j, with ι∘q_in=d_K^{j−1},
d_K^j∘ι=0, F(q_in) epic, and F(ι) a kernel of F(d_K^j).

The incoming differential factors as d_K^{j−1}=ι∘q_in. -/
  factor : q ≫ ι = K.obj.d (j - 1) j
  /-- Let E be preadditive, A abelian and F:E → A additive.
Let K be a bounded integer cochain complex in E. A degree-j cycle datum has an object Z_j and maps
q_in:K^{j−1} → Z_j, ι:Z_j → K^j, with ι∘q_in=d_K^{j−1},
d_K^j∘ι=0, F(q_in) epic, and F(ι) a kernel of F(d_K^j).

The cycle inclusion is killed by the outgoing differential: d_K^j∘ι=0. -/
  zero : ι ≫ K.obj.d j (j + 1) = 0
  /-- Let E be preadditive, A abelian and F:E → A additive.
Let K be a bounded integer cochain complex in E. A degree-j cycle datum has an object Z_j and maps
q_in:K^{j−1} → Z_j, ι:Z_j → K^j, with ι∘q_in=d_K^{j−1},
d_K^j∘ι=0, F(q_in) epic, and F(ι) a kernel of F(d_K^j).

The image F(q_in):F(K^{j−1}) → F(Z_j) is epic. -/
  mappedEpi : Epi (F.map q)
  /-- Let E be preadditive, A abelian and F:E → A additive.
Let K be a bounded integer cochain complex in E. A degree-j cycle datum has an object Z_j and maps
q_in:K^{j−1} → Z_j, ι:Z_j → K^j, with ι∘q_in=d_K^{j−1},
d_K^j∘ι=0, F(q_in) epic, and F(ι) a kernel of F(d_K^j).

The fork F(Z_j) —F(ι)→ F(K^j) is a kernel of F(d_K^j). -/
  mappedIsLimit : IsLimit (KernelFork.ofι (f := F.map (K.obj.d j (j + 1)))
    (F.map ι) (by rw [← F.map_comp, zero, F.map_zero]))

variable (K : Bounded E) (a b : ℤ)
variable (hSupport : ∀ j : ℤ, j < a ∨ b < j → IsZero (K.obj.X j))
variable (hK : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic)

/-- Let E be preadditive, A abelian and F:E → A additive.
Let K be a bounded integer cochain complex in E. Suppose K is supported in [a,b] and F(K) is acyclic.

The top-degree cycle datum has Z_b=K^b, inclusion 1_{K^b} and incoming map d_K^{b−1}. -/
def topData : CycleData F K b := by
  have hd : K.obj.d b (b + 1) = 0 :=
    (hSupport (b + 1) (Or.inr (by omega))).eq_of_tgt _ _
  refine
    { Z := K.obj.X b
      ι := 𝟙 _
      q := K.obj.d (b - 1) b
      factor := Category.comp_id _
      zero := by simpa only [Category.id_comp] using hd
      mappedEpi := mappedDifferential_epi_of_acyclic_of_isZero_succ F K b
        (hSupport (b + 1) (Or.inr (by omega))) hK
      mappedIsLimit := ?_ }
  have hMapped : F.map (K.obj.d b (b + 1)) = 0 := by rw [hd, F.map_zero]
  simpa only [F.map_id] using KernelFork.IsLimit.ofId (F.map (K.obj.d b (b + 1))) hMapped

variable [F.Full] [F.Faithful]
variable (hKernelClosure : ∀ {U V : A} (f : U ⟶ V) [Epi f],
  F.essImage U → F.essImage V → F.essImage (kernel f))

namespace CycleData

variable {F K} {j : ℤ}

/-- Let E be preadditive, A abelian and F:E → A additive.
Let K be a bounded integer cochain complex in E. A degree-j cycle datum has an object Z_j and maps
q_in:K^{j−1} → Z_j, ι:Z_j → K^j, with ι∘q_in=d_K^{j−1},
d_K^j∘ι=0, F(q_in) epic, and F(ι) a kernel of F(d_K^j).

An equality j=k gives the corresponding identification of the same cycle datum in degree k. -/
def castIndex {k : ℤ} (e : j = k) (D : CycleData F K j) : CycleData F K k := e ▸ D

/-- Let E be preadditive, A abelian and F:E → A additive.
Let K be a bounded integer cochain complex in E. Assume F is fully faithful and its essential image is closed under
kernels of epimorphisms between objects in that image. Let D_j be a degree-j cycle datum.

The represented source kernel of q_in,j:K^{j−1} → Z_j, whose F-image is the ambient kernel of the epic map F(q_in,j). -/
def quotientKernelLift (D : CycleData F K j) : Functor.KernelLift F D.q := by
  let _ := D.mappedEpi
  exact F.kernelLiftOfEpi hKernelClosure D.q

/-- Let E be preadditive, A abelian and F:E → A additive.
Let K be a bounded integer cochain complex in E. Assume F is fully faithful and its essential image is closed under
kernels of epimorphisms between objects in that image. Let D_j be a degree-j cycle datum and assume F(K) is acyclic.

The predecessor datum in degree j−1 uses the represented kernel of q_in,j as its source-cycle object and its kernel inclusion as the new cycle inclusion. -/
def predecessor (D : CycleData F K j)
    (hAcyclic : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    CycleData F K (j - 1) := by
  let lift := quotientKernelLift hKernelClosure D
  let _ : Mono (F.map D.ι) := Fork.IsLimit.mono D.mappedIsLimit
  let dHigh := K.obj.d (j - 1 - 1) (j - 1)
  let dLow := K.obj.d (j - 1) j
  have hzero : lift.ι ≫ dLow = 0 := by
    dsimp only [dLow]
    rw [← D.factor, ← Category.assoc, lift.zero, zero_comp]
  have hfactorMap : F.map dLow = F.map D.q ≫ F.map D.ι := by
    dsimp only [dLow]
    rw [← F.map_comp, D.factor]
  let hKernel : IsLimit (KernelFork.ofι (f := F.map dLow) (F.map lift.ι)
      (by rw [← F.map_comp, hzero, F.map_zero])) :=
    isKernelCompMono lift.mappedIsLimit (F.map D.ι) hfactorMap
  have hdd : F.map dHigh ≫ F.map dLow = 0 := by
    rw [← F.map_comp]
    change F.map (K.obj.d (j - 1 - 1) (j - 1) ≫ K.obj.d (j - 1) j) = 0
    rw [K.obj.d_comp_d, F.map_zero]
  let l := KernelFork.IsLimit.lift' hKernel (F.map dHigh) hdd
  let qNext : K.obj.X (j - 1 - 1) ⟶ lift.K := F.preimage l.1
  have hmapqNext : F.map qNext = l.1 := F.map_preimage _
  have hfactor : qNext ≫ lift.ι = dHigh := by
    apply F.map_injective
    rw [F.map_comp, hmapqNext]
    simpa only [KernelFork.ι_ofι] using l.2
  let M := (F.mapHomologicalComplex (.up ℤ)).obj K.obj
  let S : ShortComplex A := ShortComplex.mk (F.map dHigh) (F.map dLow) hdd
  have hExact : S.Exact := by
    have h := (M.exactAt_iff' (j - 1 - 1) (j - 1) j (by simp) (by simp)).mp
      (hAcyclic (j - 1))
    let e : M.sc' (j - 1 - 1) (j - 1) j ≅ S :=
      ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (Iso.refl _)
        (by change 𝟙 _ ≫ F.map dHigh = F.map dHigh ≫ 𝟙 _; simp)
        (by change 𝟙 _ ≫ F.map dLow = F.map dLow ≫ 𝟙 _; simp)
    exact ShortComplex.exact_of_iso e h
  let _ : Epi (kernel.lift (F.map dLow) (F.map dHigh) hdd) :=
    S.exact_iff_epi_kernel_lift.mp hExact
  let e : F.obj lift.K ≅ kernel (F.map dLow) :=
    hKernel.conePointUniqueUpToIso
      (t := KernelFork.ofι (kernel.ι (F.map dLow)) (kernel.condition (F.map dLow)))
      (kernelIsKernel (F.map dLow))
  have he := IsLimit.conePointUniqueUpToIso_hom_comp hKernel
    (kernelIsKernel (F.map dLow)) WalkingParallelPair.zero
  have he' : e.hom ≫ kernel.ι (F.map dLow) = F.map lift.ι := he
  have hlCanonical : l.1 ≫ e.hom = kernel.lift (F.map dLow) (F.map dHigh) hdd := by
    apply (cancel_mono (kernel.ι (F.map dLow))).mp
    rw [Category.assoc, he']
    have hl : l.1 ≫ F.map lift.ι = F.map dHigh := by
      simpa only [KernelFork.ι_ofι] using l.2
    rw [hl, kernel.lift_ι]
  have hlEq : l.1 = kernel.lift (F.map dLow) (F.map dHigh) hdd ≫ e.inv := by
    apply (cancel_mono e.hom).mp
    rw [hlCanonical, Category.assoc, e.inv_hom_id, Category.comp_id]
  have hlEpi : Epi l.1 := by
    rw [hlEq]
    infer_instance
  have hqEpi : Epi (F.map qNext) := by rw [hmapqNext]; exact hlEpi
  exact
    { Z := lift.K
      ι := lift.ι
      q := qNext
      factor := hfactor
      zero := by
        rw [sub_add_cancel]
        exact hzero
      mappedEpi := hqEpi
      mappedIsLimit := KernelFork.isLimitOfIsLimitOfIff' hKernel
        (F.map (K.obj.d (j - 1) (j - 1 + 1))) (by
          intro W φ
          have h (k : ℤ) (hk : k = j) :
              φ ≫ F.map (K.obj.d (j - 1) j) = 0 ↔
                φ ≫ F.map (K.obj.d (j - 1) k) = 0 := by
            subst k
            rfl
          exact h _ (by omega)) }

/-- Let E be preadditive, A abelian and F:E → A additive.
Let K be a bounded integer cochain complex in E. Assume F is fully faithful and its essential image is closed under
kernels of epimorphisms between objects in that image. Let D_j be a degree-j cycle datum and F(K) acyclic.

The source object of the predecessor datum is the object representing Ker(F(q_in,j)) through the canonical source kernel lift. -/
theorem predecessor_Z (D : CycleData F K j)
    (hAcyclic : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    (predecessor hKernelClosure D hAcyclic).Z = (quotientKernelLift hKernelClosure D).K := rfl

/-- Let E be preadditive, A abelian and F:E → A additive.
Let K be a bounded integer cochain complex in E. Assume F is fully faithful and its essential image is closed under
kernels of epimorphisms between objects in that image. Let D_j be a degree-j cycle datum and F(K) acyclic.

The inclusion of the predecessor cycles into K^{j−1} is the inclusion of the represented source kernel of q_in,j. -/
theorem predecessor_ι (D : CycleData F K j)
    (hAcyclic : ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic) :
    (predecessor hKernelClosure D hAcyclic).ι = (quotientKernelLift hKernelClosure D).ι := rfl

variable [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
  [F.ReflectsAdmissibleExact]

/-- Let E be preadditive, A abelian and F:E → A additive.
Let K be a bounded integer cochain complex in E. Assume F is fully faithful and its essential image is closed under
kernels of epimorphisms between objects in that image. Assume E is Quillen exact with a zero object and binary biproducts, and F reflects admissible exactness. Let D_j be a cycle datum.

The represented kernel row Ker(q_in,j) → K^{j−1} → Z_j is admissible exact in E. -/
theorem predecessor_row_isAdmissibleExact (D : CycleData F K j) :
    IsAdmissibleExact (quotientKernelLift hKernelClosure D).shortComplex := by
  let _ := D.mappedEpi
  exact (quotientKernelLift hKernelClosure D).isAdmissibleExact

end CycleData

/-- For an integer b, define a descending degree sequence indexed by n∈ℕ.

The sequence starts at b and decreases by one at each step. -/
def degree (b : ℤ) : ℕ → ℤ := Nat.rec b (fun _ j => j - 1)

/-- For b∈ℤ and n∈ℕ, let degree(b,n) be the sequence starting at b and decreasing by one.

Its closed formula is degree(b,n)=b−n. -/
theorem degree_eq (b : ℤ) (n : ℕ) : degree b n = b - (n : ℤ) := by
  induction n with
  | zero => simp only [degree, Nat.rec_zero, Nat.cast_zero, sub_zero]
  | succ n ih =>
    change degree b n - 1 = b - (↑(n + 1) : ℤ)
    rw [ih]
    omega

/-- Let E be preadditive, A abelian and F:E → A additive.
Let K be a bounded integer cochain complex in E. Assume F is fully faithful and its essential image is closed under
kernels of epimorphisms between objects in that image. Fix a term-support interval [a,b] for K and assume F(K) is acyclic.
Write D_j=(Z_j,ι_j,q_in,j) for the constructed source-cycle data,
where ι_j:Z_j → K^j and q_in,j:K^{j−1} → Z_j.

The recursive cycle datum at step n has degree b−n, begins with the top datum and is obtained by repeated predecessor construction. -/
def boundary : (n : ℕ) → CycleData F K (degree b n) :=
  Nat.rec (topData F K a b hSupport hK)
    (fun _ D => D.predecessor hKernelClosure hK)

/-- Let E be preadditive, A abelian and F:E → A additive.
Let K be a bounded integer cochain complex in E. Assume F is fully faithful and its essential image is closed under
kernels of epimorphisms between objects in that image. Fix a term-support interval [a,b] for K and assume F(K) is acyclic.
Write D_j=(Z_j,ι_j,q_in,j) for the constructed source-cycle data,
where ι_j:Z_j → K^j and q_in,j:K^{j−1} → Z_j.

At step zero the recursive datum is the top datum on K^b. -/
theorem boundary_zero : boundary F K a b hSupport hK hKernelClosure 0 =
    topData F K a b hSupport hK := rfl

/-- Let E be preadditive, A abelian and F:E → A additive.
Let K be a bounded integer cochain complex in E. Assume F is fully faithful and its essential image is closed under
kernels of epimorphisms between objects in that image. Fix a term-support interval [a,b] for K and assume F(K) is acyclic.
Write D_j=(Z_j,ι_j,q_in,j) for the constructed source-cycle data,
where ι_j:Z_j → K^j and q_in,j:K^{j−1} → Z_j.

The datum at step n+1 is the predecessor of the datum at step n. -/
theorem boundary_succ (n : ℕ) :
    boundary F K a b hSupport hK hKernelClosure (n + 1) =
      (boundary F K a b hSupport hK hKernelClosure n).predecessor hKernelClosure hK := rfl

/-- Let b,j∈ℤ with j≤b and degree(b,n)=b−n.

At the natural step count (b−j).toNat, the degree is j. -/
theorem degree_toNat (b j : ℤ) (hj : j ≤ b) : degree b (b - j).toNat = j := by
  rw [degree_eq]
  omega

/-- Let E be preadditive, A abelian and F:E → A additive.
Let K be a bounded integer cochain complex in E. Assume F is fully faithful and its essential image is closed under
kernels of epimorphisms between objects in that image. Fix a term-support interval [a,b] for K and assume F(K) is acyclic.
Write D_j=(Z_j,ι_j,q_in,j) for the constructed source-cycle data,
where ι_j:Z_j → K^j and q_in,j:K^{j−1} → Z_j.

The cycle data D_j are defined for every integer j, using the descending family for j≤b and the zero terms above b. -/
def dataAt (j : ℤ) : CycleData F K j := by
  by_cases hj : j ≤ b
  · exact CycleData.castIndex (degree_toNat b j hj)
      (boundary F K a b hSupport hK hKernelClosure (b - j).toNat)
  · exact topData F K a j (fun k hk => hSupport k (by omega)) hK

/-- Let E be preadditive, A abelian and F:E → A additive.
Let K be a bounded integer cochain complex in E. Assume F is fully faithful and its essential image is closed under
kernels of epimorphisms between objects in that image. Fix a term-support interval [a,b] for K and assume F(K) is acyclic.
Write D_j=(Z_j,ι_j,q_in,j) for the constructed source-cycle data,
where ι_j:Z_j → K^j and q_in,j:K^{j−1} → Z_j.

The outgoing map q_j:K^j → Z_{j+1} is the incoming quotient of D_{j+1}. -/
def outgoing (j : ℤ) : K.obj.X j ⟶ (dataAt F K a b hSupport hK hKernelClosure (j + 1)).Z :=
  eqToHom (congrArg K.obj.X (show j = (j + 1) - 1 by omega)) ≫
    (dataAt F K a b hSupport hK hKernelClosure (j + 1)).q

/-- Let E be preadditive, A abelian and F:E → A additive.
Let K be a bounded integer cochain complex in E. Assume F is fully faithful and its essential image is closed under
kernels of epimorphisms between objects in that image. Fix a term-support interval [a,b] for K and assume F(K) is acyclic.
Write D_j=(Z_j,ι_j,q_in,j) for the constructed source-cycle data,
where ι_j:Z_j → K^j and q_in,j:K^{j−1} → Z_j.

The outgoing differential satisfies d_K^j=ι_{j+1}∘q_j. -/
theorem outgoing_factor (j : ℤ) :
    outgoing F K a b hSupport hK hKernelClosure j ≫
      (dataAt F K a b hSupport hK hKernelClosure (j + 1)).ι = K.obj.d j (j + 1) := by
  rw [outgoing, Category.assoc,
    (dataAt F K a b hSupport hK hKernelClosure (j + 1)).factor]
  have h (i : ℤ) (hi : i = j) :
      eqToHom (congrArg K.obj.X hi.symm) ≫ K.obj.d i (j + 1) = K.obj.d j (j + 1) := by
    subst i
    simp
  exact h _ (by omega)

/-- Let E be preadditive, A abelian and F:E → A additive.
Let K be a bounded integer cochain complex in E. Assume F is fully faithful and its essential image is closed under
kernels of epimorphisms between objects in that image. Fix a term-support interval [a,b] for K and assume F(K) is acyclic.
Write D_j=(Z_j,ι_j,q_in,j) for the constructed source-cycle data,
where ι_j:Z_j → K^j and q_in,j:K^{j−1} → Z_j.

The mapped outgoing quotient F(q_j):F(K^j) → F(Z_{j+1}) is epic. -/
theorem outgoing_map_epi (j : ℤ) : Epi (F.map (outgoing F K a b hSupport hK hKernelClosure j)) := by
  let _ := (dataAt F K a b hSupport hK hKernelClosure (j + 1)).mappedEpi
  rw [outgoing, F.map_comp]
  infer_instance

/-- Let E be preadditive, A abelian and F:E → A additive.
Let K be a bounded integer cochain complex in E. Assume F is fully faithful and its essential image is closed under
kernels of epimorphisms between objects in that image. Fix a term-support interval [a,b] for K and assume F(K) is acyclic.
Write D_j=(Z_j,ι_j,q_in,j) for the constructed source-cycle data,
where ι_j:Z_j → K^j and q_in,j:K^{j−1} → Z_j.

The source inclusion ι_j:Z_j → K^j is a monomorphism. -/
theorem inclusion_mono (j : ℤ) :
    Mono (dataAt F K a b hSupport hK hKernelClosure j).ι :=
  F.mono_of_mono_map
    (Fork.IsLimit.mono (dataAt F K a b hSupport hK hKernelClosure j).mappedIsLimit)

/-- Let E be preadditive, A abelian and F:E → A additive.
Let K be a bounded integer cochain complex in E. Assume F is fully faithful and its essential image is closed under
kernels of epimorphisms between objects in that image. Fix a term-support interval [a,b] for K and assume F(K) is acyclic.
Write D_j=(Z_j,ι_j,q_in,j) for the constructed source-cycle data,
where ι_j:Z_j → K^j and q_in,j:K^{j−1} → Z_j.

The row composite q_j∘ι_j is zero. -/
theorem row_zero (j : ℤ) :
    (dataAt F K a b hSupport hK hKernelClosure j).ι ≫
      outgoing F K a b hSupport hK hKernelClosure j = 0 := by
  let _ := inclusion_mono F K a b hSupport hK hKernelClosure (j + 1)
  apply (cancel_mono (dataAt F K a b hSupport hK hKernelClosure (j + 1)).ι).mp
  rw [zero_comp, Category.assoc, outgoing_factor]
  exact (dataAt F K a b hSupport hK hKernelClosure j).zero

/-- Let E be preadditive, A abelian and F:E → A additive.
Let K be a bounded integer cochain complex in E. Assume F is fully faithful and its essential image is closed under
kernels of epimorphisms between objects in that image. Fix a term-support interval [a,b] for K and assume F(K) is acyclic.
Write D_j=(Z_j,ι_j,q_in,j) for the constructed source-cycle data,
where ι_j:Z_j → K^j and q_in,j:K^{j−1} → Z_j.

The degree-j source short complex is Z_j —ι_j→ K^j —q_j→ Z_{j+1}. -/
abbrev row (j : ℤ) : ShortComplex E :=
  ShortComplex.mk (dataAt F K a b hSupport hK hKernelClosure j).ι
    (outgoing F K a b hSupport hK hKernelClosure j)
    (row_zero F K a b hSupport hK hKernelClosure j)

/-- Let E be preadditive, A abelian and F:E → A additive.
Let K be a bounded integer cochain complex in E. Assume F is fully faithful and its essential image is closed under
kernels of epimorphisms between objects in that image. Fix a term-support interval [a,b] for K and assume F(K) is acyclic.
Write D_j=(Z_j,ι_j,q_in,j) for the constructed source-cycle data,
where ι_j:Z_j → K^j and q_in,j:K^{j−1} → Z_j.

In A, F(ι_j) is a kernel of the mapped outgoing quotient F(q_j). -/
def mappedRowIsLimit (j : ℤ) :
    IsLimit (KernelFork.ofι (f := F.map (outgoing F K a b hSupport hK hKernelClosure j))
      (F.map (dataAt F K a b hSupport hK hKernelClosure j).ι) (by
        rw [← F.map_comp, row_zero, F.map_zero])) := by
  have hzero : F.map (dataAt F K a b hSupport hK hKernelClosure j).ι ≫
      F.map (outgoing F K a b hSupport hK hKernelClosure j) = 0 := by
    rw [← F.map_comp, row_zero, F.map_zero]
  have hfactor : F.map (outgoing F K a b hSupport hK hKernelClosure j) ≫
      F.map (dataAt F K a b hSupport hK hKernelClosure (j + 1)).ι =
      F.map (K.obj.d j (j + 1)) := by
    rw [← F.map_comp, outgoing_factor]
  exact isKernelOfComp
    (f := F.map (outgoing F K a b hSupport hK hKernelClosure j))
    (F.map (dataAt F K a b hSupport hK hKernelClosure (j + 1)).ι)
    (F.map (K.obj.d j (j + 1)))
    (dataAt F K a b hSupport hK hKernelClosure j).mappedIsLimit hzero hfactor

/-- Let E be preadditive, A abelian and F:E → A additive.
Let K be a bounded integer cochain complex in E. Assume F is fully faithful and its essential image is closed under
kernels of epimorphisms between objects in that image. Fix a term-support interval [a,b] for K and assume F(K) is acyclic.
Write D_j=(Z_j,ι_j,q_in,j) for the constructed source-cycle data,
where ι_j:Z_j → K^j and q_in,j:K^{j−1} → Z_j.

The mapped row 0 → F(Z_j) → F(K^j) → F(Z_{j+1}) → 0 is short exact. -/
theorem row_map_shortExact (j : ℤ) :
    ((row F K a b hSupport hK hKernelClosure j).map F).ShortExact := by
  let hKernel := mappedRowIsLimit F K a b hSupport hK hKernelClosure j
  have hExact : ((row F K a b hSupport hK hKernelClosure j).map F).Exact :=
    ((row F K a b hSupport hK hKernelClosure j).map F).exact_of_f_is_kernel hKernel
  exact ShortComplex.ShortExact.mk' hExact (Fork.IsLimit.mono hKernel)
    (outgoing_map_epi F K a b hSupport hK hKernelClosure j)

/-- Let E be preadditive, A abelian and F:E → A additive.
Let K be a bounded integer cochain complex in E. Assume F is fully faithful and its essential image is closed under
kernels of epimorphisms between objects in that image. Fix a term-support interval [a,b] for K and assume F(K) is acyclic.
Write D_j=(Z_j,ι_j,q_in,j) for the constructed source-cycle data,
where ι_j:Z_j → K^j and q_in,j:K^{j−1} → Z_j.

The source-cycle object Z_j is zero when j<a or b<j. -/
theorem cycles_isZero_outside (j : ℤ) (hj : j < a ∨ b < j) :
    IsZero (dataAt F K a b hSupport hK hKernelClosure j).Z := by
  let _ := inclusion_mono F K a b hSupport hK hKernelClosure j
  apply (IsZero.iff_id_eq_zero _).mpr
  apply (cancel_mono (dataAt F K a b hSupport hK hKernelClosure j).ι).mp
  simp only [Category.id_comp, zero_comp]
  exact (hSupport j hj).eq_of_tgt _ _

variable [HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
  [F.ReflectsAdmissibleExact]

/-- Let E be preadditive, A abelian and F:E → A additive.
Let K be a bounded integer cochain complex in E. Assume F is fully faithful and its essential image is closed under
kernels of epimorphisms between objects in that image. Fix a term-support interval [a,b] for K and assume F(K) is acyclic.
Write D_j=(Z_j,ι_j,q_in,j) for the constructed source-cycle data,
where ι_j:Z_j → K^j and q_in,j:K^{j−1} → Z_j. Assume E has a zero object, binary biproducts and a Quillen exact
structure, and F reflects admissible exact sequences.

Every row Z_j → K^j → Z_{j+1} is admissible exact in E. -/
theorem row_isAdmissibleExact (j : ℤ) :
    IsAdmissibleExact (row F K a b hSupport hK hKernelClosure j) :=
  F.reflects_admissibleExact _ (row_map_shortExact F K a b hSupport hK hKernelClosure j)

/-- Let E be preadditive, A abelian and F:E → A additive.
Let K be a bounded integer cochain complex in E. Assume F is fully faithful and its essential image is closed under
kernels of epimorphisms between objects in that image. Fix a term-support interval [a,b] for K and assume F(K) is acyclic.
Write D_j=(Z_j,ι_j,q_in,j) for the constructed source-cycle data,
where ι_j:Z_j → K^j and q_in,j:K^{j−1} → Z_j. Assume E has a zero object, binary biproducts and a Quillen exact
structure, and F reflects admissible exact sequences.

The inclusion ι_j is a kernel of q_j in E. -/
def rowIsLimit (j : ℤ) :
    IsLimit (KernelFork.ofι (f := outgoing F K a b hSupport hK hKernelClosure j)
      (dataAt F K a b hSupport hK hKernelClosure j).ι
      (row_zero F K a b hSupport hK hKernelClosure j)) :=
  isLimit_kernelFork_of_isAdmissibleExact
    (row_isAdmissibleExact F K a b hSupport hK hKernelClosure j)

/-- Let E be preadditive, A abelian and F:E → A additive.
Let K be a bounded integer cochain complex in E. Assume F is fully faithful and its essential image is closed under
kernels of epimorphisms between objects in that image. Fix a term-support interval [a,b] for K and assume F(K) is acyclic.
Write D_j=(Z_j,ι_j,q_in,j) for the constructed source-cycle data,
where ι_j:Z_j → K^j and q_in,j:K^{j−1} → Z_j. Assume E has a zero object, binary biproducts and a Quillen exact
structure, and F reflects admissible exact sequences.

The quotient q_j is a cokernel of ι_j in E. -/
def rowIsColimit (j : ℤ) :
    IsColimit (CokernelCofork.ofπ
      (f := (dataAt F K a b hSupport hK hKernelClosure j).ι)
      (outgoing F K a b hSupport hK hKernelClosure j)
      (row_zero F K a b hSupport hK hKernelClosure j)) :=
  isColimit_cokernelCofork_of_isAdmissibleExact
    (row_isAdmissibleExact F K a b hSupport hK hKernelClosure j)

/-- Let E be a preadditive Quillen exact category with a zero object and
binary biproducts, and K a bounded integer cochain complex.
Admissible acyclic data consist of Z_j, inclusions ι_j:Z_j → K^j
and quotients q_j:K^j → Z_{j+1}, with admissible exact rows
Z_j → K^j → Z_{j+1} and ι_{j+1}∘q_j=d_K^j.

The structure packages the all-degree source objects, inclusions, quotients, zero row composites, conflations and differential factorizations. -/
structure AdmissibleAcyclicData (K : Bounded E) where
  /-- Let E be a preadditive Quillen exact category with a zero object and
binary biproducts, and K a bounded integer cochain complex.
Admissible acyclic data consist of Z_j, inclusions ι_j:Z_j → K^j
and quotients q_j:K^j → Z_{j+1}, with admissible exact rows
Z_j → K^j → Z_{j+1} and ι_{j+1}∘q_j=d_K^j.

The family of source-cycle objects Z_j indexed by every integer j. -/
  Z : ℤ → E
  /-- Let E be a preadditive Quillen exact category with a zero object and
binary biproducts, and K a bounded integer cochain complex.
Admissible acyclic data consist of Z_j, inclusions ι_j:Z_j → K^j
and quotients q_j:K^j → Z_{j+1}, with admissible exact rows
Z_j → K^j → Z_{j+1} and ι_{j+1}∘q_j=d_K^j.

The family of cycle inclusions ι_j:Z_j → K^j. -/
  ι : ∀ j, Z j ⟶ K.obj.X j
  /-- Let E be a preadditive Quillen exact category with a zero object and
binary biproducts, and K a bounded integer cochain complex.
Admissible acyclic data consist of Z_j, inclusions ι_j:Z_j → K^j
and quotients q_j:K^j → Z_{j+1}, with admissible exact rows
Z_j → K^j → Z_{j+1} and ι_{j+1}∘q_j=d_K^j.

The family of outgoing quotients q_j:K^j → Z_{j+1}. -/
  q : ∀ j, K.obj.X j ⟶ Z (j + 1)
  /-- Let E be a preadditive Quillen exact category with a zero object and
binary biproducts, and K a bounded integer cochain complex.
Admissible acyclic data consist of Z_j, inclusions ι_j:Z_j → K^j
and quotients q_j:K^j → Z_{j+1}, with admissible exact rows
Z_j → K^j → Z_{j+1} and ι_{j+1}∘q_j=d_K^j.

The row composites satisfy q_j∘ι_j=0 in every degree. -/
  zero : ∀ j, ι j ≫ q j = 0
  /-- Let E be a preadditive Quillen exact category with a zero object and
binary biproducts, and K a bounded integer cochain complex.
Admissible acyclic data consist of Z_j, inclusions ι_j:Z_j → K^j
and quotients q_j:K^j → Z_{j+1}, with admissible exact rows
Z_j → K^j → Z_{j+1} and ι_{j+1}∘q_j=d_K^j.

Each short complex Z_j → K^j → Z_{j+1} is an admissible exact pair. -/
  admissible : ∀ j, IsAdmissibleExact (ShortComplex.mk (ι j) (q j) (zero j))
  /-- Let E be a preadditive Quillen exact category with a zero object and
binary biproducts, and K a bounded integer cochain complex.
Admissible acyclic data consist of Z_j, inclusions ι_j:Z_j → K^j
and quotients q_j:K^j → Z_{j+1}, with admissible exact rows
Z_j → K^j → Z_{j+1} and ι_{j+1}∘q_j=d_K^j.

The cochain differentials are the composites d_K^j=ι_{j+1}∘q_j. -/
  factor : ∀ j, q j ≫ ι (j + 1) = K.obj.d j (j + 1)

/-- Let E be preadditive, A abelian and F:E → A additive.
Let K be a bounded integer cochain complex in E. Assume F is fully faithful and its essential image is closed under
kernels of epimorphisms between objects in that image. Fix a term-support interval [a,b] for K and assume F(K) is acyclic.
Write D_j=(Z_j,ι_j,q_in,j) for the constructed source-cycle data,
where ι_j:Z_j → K^j and q_in,j:K^{j−1} → Z_j. Assume E has a zero object, binary biproducts and a Quillen exact
structure, and F reflects admissible exact sequences.

The constructed all-integer source cycle family gives admissible acyclic data for K. -/
def admissibleData : AdmissibleAcyclicData K where
  Z j := (dataAt F K a b hSupport hK hKernelClosure j).Z
  ι j := (dataAt F K a b hSupport hK hKernelClosure j).ι
  q j := outgoing F K a b hSupport hK hKernelClosure j
  zero := row_zero F K a b hSupport hK hKernelClosure
  admissible := row_isAdmissibleExact F K a b hSupport hK hKernelClosure
  factor := outgoing_factor F K a b hSupport hK hKernelClosure

section Converse

variable (G : E ⥤ A) [G.Additive] [G.IsExact]

/-- Let E be a preadditive Quillen exact category with a zero object and
binary biproducts, and K a bounded integer cochain complex.
Admissible acyclic data consist of Z_j, inclusions ι_j:Z_j → K^j
and quotients q_j:K^j → Z_{j+1}, with admissible exact rows
Z_j → K^j → Z_{j+1} and ι_{j+1}∘q_j=d_K^j. Let G:E → A be additive exact with A abelian.

Applying G to K gives an acyclic cochain complex. -/
theorem ambient_acyclic_of_admissibleData (D : AdmissibleAcyclicData K) :
    ((G.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic := by
  let M := (G.mapHomologicalComplex (.up ℤ)).obj K.obj
  have hAt (j : ℤ) : M.ExactAt (j + 1) := by
    let R : ShortComplex E := ShortComplex.mk (D.ι (j + 1)) (D.q (j + 1)) (D.zero (j + 1))
    have hR : (R.map G).ShortExact := G.map_admissibleExact R (D.admissible (j + 1))
    have hPrev : ((ShortComplex.mk (D.ι j) (D.q j) (D.zero j)).map G).ShortExact :=
      G.map_admissibleExact _ (D.admissible j)
    let _ : Epi (G.map (D.q j)) := hPrev.epi_g
    have hzeroE : K.obj.d j (j + 1) ≫ D.q (j + 1) = 0 := by
      rw [← D.factor j, Category.assoc, D.zero (j + 1), comp_zero]
    have hzero : G.map (K.obj.d j (j + 1)) ≫ G.map (D.q (j + 1)) = 0 := by
      rw [← G.map_comp, hzeroE, G.map_zero]
    let S : ShortComplex A :=
      ShortComplex.mk (G.map (K.obj.d j (j + 1))) (G.map (D.q (j + 1))) hzero
    let φ : S ⟶ R.map G :=
      { τ₁ := G.map (D.q j)
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _
        comm₁₂ := by
          change G.map (D.q j) ≫ G.map (D.ι (j + 1)) =
            G.map (K.obj.d j (j + 1)) ≫ 𝟙 _
          rw [Category.comp_id, ← G.map_comp, D.factor j]
        comm₂₃ := by
          change 𝟙 _ ≫ G.map (D.q (j + 1)) = G.map (D.q (j + 1)) ≫ 𝟙 _
          simp }
    have hS : S.Exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr hR.exact
    have hNext : ((ShortComplex.mk (D.ι (j + 1 + 1)) (D.q (j + 1 + 1))
        (D.zero (j + 1 + 1))).map G).ShortExact :=
      G.map_admissibleExact _ (D.admissible (j + 1 + 1))
    let _ : Mono (G.map (D.ι (j + 1 + 1))) := hNext.mono_f
    let ψ : S ⟶ M.sc' j (j + 1) (j + 1 + 1) :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := G.map (D.ι (j + 1 + 1))
        comm₁₂ := by
          change 𝟙 _ ≫ G.map (K.obj.d j (j + 1)) =
            G.map (K.obj.d j (j + 1)) ≫ 𝟙 _
          simp
        comm₂₃ := by
          change 𝟙 _ ≫ G.map (K.obj.d (j + 1) (j + 1 + 1)) =
            G.map (D.q (j + 1)) ≫ G.map (D.ι (j + 1 + 1))
          rw [Category.id_comp, ← G.map_comp, D.factor (j + 1)] }
    have hExact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).mp hS
    exact (M.exactAt_iff' j (j + 1) (j + 1 + 1) (by simp) (by simp)).mpr hExact
  intro j
  simpa only [sub_add_cancel] using hAt (j - 1)

end Converse

variable [F.IsExact]

include hKernelClosure in
/-- Let E be preadditive, A abelian and F:E → A additive.
Let K be a bounded integer cochain complex in E. Assume F is fully faithful and its essential image is closed under
kernels of epimorphisms between objects in that image. Assume E is Quillen exact with a zero object and binary biproducts, and F is exact and reflects admissible exactness.

For bounded K, F(K) is acyclic if and only if K admits admissible acyclic data in every integer degree. -/
theorem ambient_acyclic_iff_admissibleData :
    ((F.mapHomologicalComplex (.up ℤ)).obj K.obj).Acyclic ↔
      Nonempty (AdmissibleAcyclicData K) := by
  constructor
  · intro hAcyclic
    obtain ⟨a', b', hWindow⟩ := K.property
    exact ⟨admissibleData F K a' b' hWindow hAcyclic hKernelClosure⟩
  · rintro ⟨D⟩
    exact ambient_acyclic_of_admissibleData K F D

end CochainComplex.Bounded.AmbientCycles

end
