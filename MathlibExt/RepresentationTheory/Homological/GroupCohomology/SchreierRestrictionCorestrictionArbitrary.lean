/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.Algebra.Homology.LinearHomCochainComplex
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.CupProduct
public import MathlibExt.RepresentationTheory.Homological.GroupCohomology.SchreierTransferArbitraryNaturality
public import Mathlib.CategoryTheory.Abelian.Projective.Resolution

/-!
# Arbitrary restriction followed by Schreier corestriction

Restriction followed by arbitrary-degree Schreier transfer is represented
by precomposition with an explicit endomorphism of the bar resolution.  Its
augmentation is multiplication by the subgroup index, so uniqueness of
lifts between projective resolutions identifies the two maps up to chain
homotopy.  This yields the restriction--corestriction index formula in every
cohomological degree.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

open CategoryTheory
open scoped BigOperators MonoidAlgebra

namespace groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G]
variable {H : Subgroup G}

/-- A finite-index right transversal has a finite type of representatives. -/
noncomputable local instance restrictionCorestrictionArbitraryFintype
    (T : H.RightTransversal) [H.FiniteIndex] : Fintype (T : Set G) :=
  @Fintype.ofFinite (T : Set G) (T.2.finite_right)

/-- The normalized basis element of the inhomogeneous bar resolution. -/
def barBasis (n : ℕ) (g : Fin n → G) :
    (Rep.barComplex k G).X n :=
  Finsupp.single g (MonoidAlgebra.single 1 1)

theorem freeLift_barBasis (A : Rep k G) (n : ℕ)
    (f : (Fin n → G) → A) (g : Fin n → G) :
    (Rep.freeLift k G A f).hom (barBasis (k := k) n g) = f g := by
  simp [barBasis]

/-- The universal normalized bar-basis cochain. -/
def barBasisCochain (n : ℕ) :
    (Fin n → G) → (Rep.barComplex k G).X n :=
  barBasis (k := k) n

/-- Free extension of the universal normalized bar-basis cochain is the
identity of the corresponding free representation. -/
theorem freeLift_barBasisCochain (n : ℕ) :
    Rep.freeLift k G ((Rep.barComplex k G).X n)
        (barBasisCochain (k := k) (G := G) n) =
      𝟙 ((Rep.barComplex k G).X n) := by
  apply Rep.free_ext k G ((Rep.barComplex k G).X n)
  intro g
  simp [barBasisCochain, barBasis]

/-- The normalized bar basis restricted from `G`-tuples to `H`-tuples. -/
def restrictedBarBasisCochain (n : ℕ) :
    (Fin n → H) → (Rep.barComplex k G).X n :=
  fun q ↦ barBasis (k := k) n (fun i ↦ (q i : G))

/-- Restricting the universal ambient bar-basis cochain gives the universal
subgroup-indexed bar-basis cochain. -/
theorem cochainsMap_barBasisCochain (n : ℕ) :
    ((groupCohomology.cochainsMap (Subgroup.subtype H)
      (𝟙 (Rep.res (Subgroup.subtype H)
        ((Rep.barComplex k G).X n)))).f n).hom
        (barBasisCochain (k := k) (G := G) n) =
      restrictedBarBasisCochain (k := k) (G := G) (H := H) n :=
  rfl

/-- Degree-`n` component of the bar-chain endomorphism representing
restriction followed by chosen-transversal corestriction. -/
noncomputable def restrictionCorestrictionChainComponent
    (T : H.RightTransversal) [H.FiniteIndex] (n : ℕ) :
    (Rep.barComplex k G).X n ⟶ (Rep.barComplex k G).X n :=
  Rep.freeLift k G ((Rep.barComplex k G).X n)
    (corestrictionCochain ((Rep.barComplex k G).X n) T n
      (restrictedBarBasisCochain (k := k) (G := G) (H := H) n))

@[simp]
theorem restrictionCorestrictionChainComponent_barBasis
    (T : H.RightTransversal) [H.FiniteIndex] (n : ℕ)
    (g : Fin n → G) :
    (restrictionCorestrictionChainComponent (k := k) T n).hom
        (barBasis (k := k) n g) =
      corestrictionCochain ((Rep.barComplex k G).X n) T n
        (restrictedBarBasisCochain (k := k) (G := G) (H := H) n) g := by
  simp [restrictionCorestrictionChainComponent, barBasis]

/-- Precomposition by the universal transfer-chain component is restriction
followed by arbitrary Schreier transfer on every coefficient cochain. -/
theorem restrictionCorestrictionChainComponent_comp_freeLift
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (n : ℕ) (f : (Fin n → G) → A) :
    restrictionCorestrictionChainComponent (k := k) T n ≫
        Rep.freeLift k G A f =
      Rep.freeLift k G A
        (corestrictionCochain A T n
          (fun q ↦ f (fun i ↦ (q i : G)))) := by
  apply Rep.free_ext k G A
  intro g
  change (Rep.freeLift k G A f).hom
      ((restrictionCorestrictionChainComponent (k := k) T n).hom
        (barBasis (k := k) n g)) =
    (Rep.freeLift k G A
      (corestrictionCochain A T n
        (fun q ↦ f (fun i ↦ (q i : G))))).hom
      (barBasis (k := k) n g)
  rw [restrictionCorestrictionChainComponent_barBasis,
    freeLift_barBasis]
  have h := congrFun
    (corestrictionCochain_naturality (Rep.freeLift k G A f) T n
      (restrictedBarBasisCochain (k := k) (G := G) (H := H) n)) g
  have hbasis :
      (fun q : Fin n → H ↦
        (Rep.freeLift k G A f).hom
          (restrictedBarBasisCochain
            (k := k) (G := G) (H := H) n q)) =
        (fun q ↦ f (fun i ↦ (q i : G))) := by
    funext q
    exact freeLift_barBasis A n f (fun i ↦ (q i : G))
  rw [hbasis] at h
  exact h

/-- Precomposition by the bar differential is the inhomogeneous cochain
differential under the free-lift equivalence. -/
theorem barComplex_d_comp_freeLift
    (A : Rep k G) (n : ℕ) (f : (Fin n → G) → A) :
    (Rep.barComplex k G).d (n + 1) n ≫
        Rep.freeLift k G A f =
      Rep.freeLift k G A
        ((inhomogeneousCochains.d A n).hom f) := by
  apply Rep.free_ext k G A
  intro g
  change (Rep.freeLift k G A f).hom
      (((Rep.barComplex k G).d (n + 1) n).hom
        (barBasis (k := k) (n + 1) g)) =
    (Rep.freeLift k G A
      ((inhomogeneousCochains.d A n).hom f)).hom
      (barBasis (k := k) (n + 1) g)
  rw [freeLift_barBasis]
  rw [Rep.barComplex.d_def]
  simp only [barBasis]
  rw [Rep.barComplex.d_single]
  simp only [map_add, map_sum,
    inhomogeneousCochains.d_hom_apply]
  change Representation.freeLift A.ρ f
      (Finsupp.single (fun i ↦ g i.succ)
        (MonoidAlgebra.single (g 0) 1)) +
      ∑ j : Fin (n + 1), Representation.freeLift A.ρ f
        (Finsupp.single (Fin.contractNth j (fun x y : G ↦ x * y) g)
          (MonoidAlgebra.single 1 ((-1 : k) ^ ((j : ℕ) + 1)))) = _
  simp only [Representation.freeLift_single_single, one_smul,
    map_one, Module.End.one_apply]

/-- The universal cochain represented by the degree-`n` bar differential. -/
def barDifferentialCochain (n : ℕ) :
    (Fin (n + 1) → G) → (Rep.barComplex k G).X n :=
  (inhomogeneousCochains.d ((Rep.barComplex k G).X n) n).hom
    (barBasisCochain (k := k) (G := G) n)

/-- Free extension of the universal differential cochain is the bar
differential itself. -/
theorem freeLift_barDifferentialCochain (n : ℕ) :
    Rep.freeLift k G ((Rep.barComplex k G).X n)
        (barDifferentialCochain (k := k) (G := G) n) =
      (Rep.barComplex k G).d (n + 1) n := by
  have h := barComplex_d_comp_freeLift
    ((Rep.barComplex k G).X n) n
      (barBasisCochain (k := k) (G := G) n)
  rw [freeLift_barBasisCochain, Category.comp_id] at h
  exact h.symm

/-- The subgroup differential of the restricted universal basis cochain is
the restriction of the ambient universal differential cochain. -/
theorem inhomogeneous_d_restrictedBarBasisCochain (n : ℕ) :
    (inhomogeneousCochains.d
      (Rep.res (Subgroup.subtype H) ((Rep.barComplex k G).X n)) n).hom
        (restrictedBarBasisCochain (k := k) (G := G) (H := H) n) =
      fun q ↦ barDifferentialCochain (k := k) (G := G) n
        (fun i ↦ (q i : G)) := by
  funext q
  simp only [restrictedBarBasisCochain, barDifferentialCochain,
    barBasisCochain, inhomogeneousCochains.d_hom_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 2
  have h := Fin.comp_contractNth
    (fun x y : H ↦ x * y) (fun x y : G ↦ x * y)
    (fun x y ↦ (Subgroup.subtype H).map_mul x y) j q
  funext i
  exact congrFun h i

/-- Consecutive universal transfer-chain components commute with the bar
differential. -/
theorem restrictionCorestrictionChainComponent_comm
    (T : H.RightTransversal) [H.FiniteIndex] (n : ℕ) :
    restrictionCorestrictionChainComponent (k := k) T (n + 1) ≫
        (Rep.barComplex k G).d (n + 1) n =
      (Rep.barComplex k G).d (n + 1) n ≫
        restrictionCorestrictionChainComponent (k := k) T n := by
  let U := restrictedBarBasisCochain
    (k := k) (G := G) (H := H) n
  let C := corestrictionCochain ((Rep.barComplex k G).X n) T n U
  have hrestricted :
      (inhomogeneousCochains.d
        (Rep.res (Subgroup.subtype H) ((Rep.barComplex k G).X n)) n).hom U =
        fun q ↦ barDifferentialCochain (k := k) (G := G) n
          (fun i ↦ (q i : G)) := by
    exact inhomogeneous_d_restrictedBarBasisCochain
      (k := k) (G := G) (H := H) n
  have hcor := corestrictionCochain_d
    ((Rep.barComplex k G).X n) T n U
  rw [hrestricted] at hcor
  calc
    restrictionCorestrictionChainComponent (k := k) T (n + 1) ≫
          (Rep.barComplex k G).d (n + 1) n =
        restrictionCorestrictionChainComponent (k := k) T (n + 1) ≫
          Rep.freeLift k G ((Rep.barComplex k G).X n)
            (barDifferentialCochain (k := k) (G := G) n) := by
      rw [freeLift_barDifferentialCochain]
    _ = Rep.freeLift k G ((Rep.barComplex k G).X n)
        (corestrictionCochain ((Rep.barComplex k G).X n) T (n + 1)
          (fun q ↦ barDifferentialCochain (k := k) (G := G) n
            (fun i ↦ (q i : G)))) :=
      restrictionCorestrictionChainComponent_comp_freeLift
        ((Rep.barComplex k G).X n) T (n + 1)
          (barDifferentialCochain (k := k) (G := G) n)
    _ = Rep.freeLift k G ((Rep.barComplex k G).X n)
        ((inhomogeneousCochains.d ((Rep.barComplex k G).X n) n).hom C) := by
      rw [hcor]
    _ = (Rep.barComplex k G).d (n + 1) n ≫
        Rep.freeLift k G ((Rep.barComplex k G).X n) C := by
      rw [barComplex_d_comp_freeLift]
    _ = (Rep.barComplex k G).d (n + 1) n ≫
        restrictionCorestrictionChainComponent (k := k) T n := rfl

/-- The literal bar-chain endomorphism representing restriction followed by
chosen-transversal Schreier corestriction in every degree. -/
noncomputable def restrictionCorestrictionBarChain
    (T : H.RightTransversal) [H.FiniteIndex] :
    Rep.barComplex k G ⟶ Rep.barComplex k G where
  f n := restrictionCorestrictionChainComponent (k := k) T n
  comm' i j hij := by
    rcases hij with ⟨rfl⟩
    exact restrictionCorestrictionChainComponent_comm T j

@[simp]
theorem restrictionCorestrictionBarChain_f
    (T : H.RightTransversal) [H.FiniteIndex] (n : ℕ) :
    (restrictionCorestrictionBarChain (k := k) T).f n =
      restrictionCorestrictionChainComponent (k := k) T n :=
  rfl

/-- The same bar-chain endomorphism, typed on the exact complex carried by
Mathlib's bundled bar projective resolution. -/
noncomputable def restrictionCorestrictionChain
    (T : H.RightTransversal) [H.FiniteIndex] :
    (Rep.barResolution k G).complex ⟶
      (Rep.barResolution k G).complex := by
  rw [Rep.barResolution_complex]
  exact restrictionCorestrictionBarChain (k := k) T

@[simp]
theorem restrictionCorestrictionChain_f
    (T : H.RightTransversal) [H.FiniteIndex] (n : ℕ) :
    (restrictionCorestrictionChain (k := k) T).f n =
      restrictionCorestrictionChainComponent (k := k) T n :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
/-- The bar-resolution augmentation takes the normalized degree-zero basis
to one. -/
theorem barResolution_augmentation_barBasis_zero :
    ((Rep.barResolution k G).π.f 0).hom
        (barBasis (k := k) 0 Fin.elim0) = (1 : k) := by
  change (Rep.standardComplex.ε k G).hom
    (((Rep.barComplex.isoStandardComplex k G).hom.f 0).hom
      (barBasis (k := k) 0 Fin.elim0)) = 1
  rw [barBasis, barComplex_isoStandardComplex_hom_apply_single]
  simp [Rep.standardComplex.ε]

set_option backward.isDefEq.respectTransparency false in
/-- At degree zero, augmenting the universal restriction--corestriction
chain component gives the subgroup index. -/
theorem restrictionCorestrictionChainComponent_zero_augmentation
    (T : H.RightTransversal) [H.FiniteIndex] :
    ((Rep.barResolution k G).π.f 0).hom
        ((restrictionCorestrictionChainComponent (k := k) T 0).hom
          (barBasis (k := k) 0 Fin.elim0)) = (H.index : k) := by
  rw [restrictionCorestrictionChainComponent_barBasis,
    corestrictionCochain_apply]
  let aug : (Rep.barComplex k G).X 0 ⟶ Rep.trivial k G k :=
    (Rep.barComplex.isoStandardComplex k G).hom.f 0 ≫
      Rep.standardComplex.ε k G
  change aug.hom
      (∑ t : (T : Set G),
        ((Rep.barComplex k G).X 0).ρ (t : G)⁻¹
          (restrictedBarBasisCochain
            (k := k) (G := G) (H := H) 0
            (T.schreierFactorTuple t Fin.elim0))) = (H.index : k)
  rw [map_sum]
  have hterm (t : (T : Set G)) :
      aug.hom
          (((Rep.barComplex k G).X 0).ρ (t : G)⁻¹
            (restrictedBarBasisCochain
              (k := k) (G := G) (H := H) 0
              (T.schreierFactorTuple t Fin.elim0))) = (1 : k) := by
    rw [Rep.hom_comm_apply]
    simp only [Representation.trivial_apply]
    have hbasis :
        restrictedBarBasisCochain
            (k := k) (G := G) (H := H) 0
            (T.schreierFactorTuple t Fin.elim0) =
          barBasis (k := k) 0 Fin.elim0 := by
      unfold restrictedBarBasisCochain
      congr 2
      funext i
      exact Fin.elim0 i
    rw [hbasis]
    dsimp only [aug]
    exact barResolution_augmentation_barBasis_zero
  simp_rw [hterm]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  have hcard : Fintype.card (T : Set G) = H.index := by
    rw [Fintype.card_eq_nat_card, T.2.card_right]
  rw [hcard]

set_option backward.isDefEq.respectTransparency false in
/-- Degree-zero augmentation square for the universal
restriction--corestriction chain component. -/
theorem restrictionCorestrictionChainComponent_zero_comp_augmentation
    (T : H.RightTransversal) [H.FiniteIndex] :
    restrictionCorestrictionChainComponent (k := k) T 0 ≫
        (Rep.barResolution k G).π.f 0 =
      H.index • (Rep.barResolution k G).π.f 0 := by
  apply Rep.free_ext k G (Rep.trivial k G k)
  intro g
  have hg : g = (Fin.elim0 : Fin 0 → G) := Subsingleton.elim _ _
  subst g
  change ((Rep.barResolution k G).π.f 0).hom
      ((restrictionCorestrictionChainComponent (k := k) T 0).hom
        (barBasis (k := k) 0 Fin.elim0)) =
    H.index •
      ((Rep.barResolution k G).π.f 0).hom
        (barBasis (k := k) 0 Fin.elim0)
  rw [restrictionCorestrictionChainComponent_zero_augmentation,
    barResolution_augmentation_barBasis_zero]
  change (H.index : k) = H.index • (1 : k)
  simp

set_option backward.isDefEq.respectTransparency false in
/-- The universal restriction--corestriction bar-chain map lifts
multiplication by the subgroup index on the resolved trivial
representation. -/
theorem restrictionCorestrictionChain_comp_augmentation
    (T : H.RightTransversal) [H.FiniteIndex] :
    restrictionCorestrictionChain (k := k) T ≫
        (Rep.barResolution k G).π =
      (Rep.barResolution k G).π ≫
        (ChainComplex.single₀ (Rep k G)).map
          (H.index • 𝟙 (Rep.trivial k G k)) := by
  apply HomologicalComplex.Hom.ext
  funext n
  cases n with
  | zero =>
      change restrictionCorestrictionChainComponent (k := k) T 0 ≫
          (Rep.barResolution k G).π.f 0 =
        (Rep.barResolution k G).π.f 0 ≫
          (H.index • 𝟙 (Rep.trivial k G k))
      rw [restrictionCorestrictionChainComponent_zero_comp_augmentation]
      simp
  | succ n => simp

/-- The scalar identity bar-chain endomorphism lifts the same index
multiplication map. -/
theorem indexSMulIdentityChain_comp_augmentation :
    (H.index • 𝟙 (Rep.barResolution k G).complex) ≫
        (Rep.barResolution k G).π =
      (Rep.barResolution k G).π ≫
        (ChainComplex.single₀ (Rep k G)).map
          (H.index • 𝟙 (Rep.trivial k G k)) := by
  rw [Functor.map_nsmul]
  simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
    Category.id_comp]
  rw [(ChainComplex.single₀ (Rep k G)).map_id, Category.comp_id]

set_option backward.isDefEq.respectTransparency false in
/-- The universal restriction--corestriction bar-chain endomorphism is
homotopic to subgroup-index multiplication. -/
noncomputable def restrictionCorestrictionChainHomotopy
    (T : H.RightTransversal) [H.FiniteIndex] :
    Homotopy
      (restrictionCorestrictionChain (k := k) T)
      (H.index • 𝟙 (Rep.barResolution k G).complex) :=
  ProjectiveResolution.liftHomotopy
    (H.index • 𝟙 (Rep.trivial k G k))
    (restrictionCorestrictionChain (k := k) T)
    (H.index • 𝟙 (Rep.barResolution k G).complex)
    (restrictionCorestrictionChain_comp_augmentation T)
    (indexSMulIdentityChain_comp_augmentation (H := H))

/-- Restriction followed by arbitrary chosen-transversal corestriction as
an endomorphism of the inhomogeneous cochain complex. -/
noncomputable def restrictionCorestrictionCochains
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex] :
    inhomogeneousCochains A ⟶ inhomogeneousCochains A :=
  groupCohomology.cochainsMap (Subgroup.subtype H)
      (𝟙 (Rep.res (Subgroup.subtype H) A)) ≫
    corestrictionCochains A T

@[simp]
theorem restrictionCorestrictionCochains_f_apply
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (n : ℕ) (f : (Fin n → G) → A) :
    ((restrictionCorestrictionCochains A T).f n).hom f =
      corestrictionCochain A T n
        (fun q ↦ f (fun i ↦ (q i : G))) :=
  rfl

/-- The bar linear-Hom cochain endomorphism obtained by precomposition with
the universal restriction--corestriction chain map. -/
noncomputable def linearHomCochainComplexObjIso
    (A : Rep k G) (P : ChainComplex (Rep k G) ℕ) :
    (HomologicalComplex.linearHomCochainComplexFunctor
      k (Rep k G) A).obj (Opposite.op P) ≅
      P.linearYonedaObj k A :=
  eqToIso (by rfl)

/-- The literal bar linear-Yoneda complex and the one carried by the bundled
bar resolution differ only by the recorded equality of their chain
complexes. -/
noncomputable def barResolutionLinearYonedaIso (A : Rep k G) :
    (Rep.barComplex k G).linearYonedaObj k A ≅
      (Rep.barResolution k G).complex.linearYonedaObj k A :=
  eqToIso (congrArg (fun P : ChainComplex (Rep k G) ℕ ↦
    P.linearYonedaObj k A) (Rep.barResolution_complex k G).symm)

/-- The inhomogeneous comparison with codomain the exact linear-Hom object
of the bundled bar resolution. -/
noncomputable def inhomogeneousResolutionLinearHomCochainIso
    (A : Rep k G) :
    inhomogeneousCochains A ≅
      (HomologicalComplex.linearHomCochainComplexFunctor
        k (Rep k G) A).obj
          (Opposite.op (Rep.barResolution k G).complex) :=
  inhomogeneousCochainsIso A ≪≫
    barResolutionLinearYonedaIso A ≪≫
    (linearHomCochainComplexObjIso A
      (Rep.barResolution k G).complex).symm

/-- The exact-resolution linear-Hom cochain endomorphism obtained by
precomposition with the universal restriction--corestriction chain map. -/
noncomputable def restrictionCorestrictionResolutionCochains
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex] :
    (HomologicalComplex.linearHomCochainComplexFunctor
      k (Rep k G) A).obj
        (Opposite.op (Rep.barResolution k G).complex) ⟶
      (HomologicalComplex.linearHomCochainComplexFunctor
        k (Rep k G) A).obj
          (Opposite.op (Rep.barResolution k G).complex) :=
  (HomologicalComplex.linearHomCochainComplexFunctor
    k (Rep k G) A).map
      (restrictionCorestrictionChain (k := k) T).op

theorem restrictionCorestrictionResolutionCochains_f_apply
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex]
    (n : ℕ)
    (phi : (Rep.barResolution k G).complex.X n ⟶ A) :
    ((restrictionCorestrictionResolutionCochains A T).f n).hom phi =
      (restrictionCorestrictionChain (k := k) T).f n ≫ phi :=
  rfl

/-- The exact-resolution linear-Hom model of restriction--corestriction is homotopic to
index multiplication in every cochain degree. -/
noncomputable def restrictionCorestrictionResolutionCochainsHomotopy
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex] :
    Homotopy
      (restrictionCorestrictionResolutionCochains A T)
      (H.index • 𝟙
        ((HomologicalComplex.linearHomCochainComplexFunctor
          k (Rep k G) A).obj
            (Opposite.op (Rep.barResolution k G).complex))) := by
  let h := (restrictionCorestrictionChainHomotopy
    (k := k) T).mapLinearHomCochainComplex k A
  let P := (Rep.barResolution k G).complex
  let F := HomologicalComplex.linearHomCochainComplexFunctor k (Rep k G) A
  have hscalar : F.map (H.index • 𝟙 P).op = H.index • 𝟙 (F.obj (Opposite.op P)) := by
    have hop : (H.index • 𝟙 P).op = H.index • (𝟙 P).op :=
      map_nsmul (CategoryTheory.opHom P P) _ _
    rw [hop, F.map_nsmul]
    change H.index • F.map (𝟙 (Opposite.op P)) = _
    rw [F.map_id]
  rw [hscalar] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- Under the bundled-resolution linear-Hom comparison, restriction followed by
Schreier transfer is precomposition by the universal bar-chain map. -/
theorem restrictionCorestrictionCochains_comp_resolutionLinearHomIso_hom
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex] :
    restrictionCorestrictionCochains A T ≫
        (inhomogeneousResolutionLinearHomCochainIso A).hom =
      (inhomogeneousResolutionLinearHomCochainIso A).hom ≫
        restrictionCorestrictionResolutionCochains A T := by
  ext n f
  change Rep.freeLift k G A
      (corestrictionCochain A T n
        (fun q ↦ f (fun i ↦ (q i : G)))) =
    restrictionCorestrictionChainComponent (k := k) T n ≫
      Rep.freeLift k G A f
  exact (restrictionCorestrictionChainComponent_comp_freeLift
    A T n f).symm

set_option backward.isDefEq.respectTransparency false in
/-- Conjugating the projective-resolution homotopy by the inhomogeneous
comparison gives equality of the induced homology maps. -/
theorem homologyMap_restrictionCorestrictionCochains
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex] (n : ℕ) :
    HomologicalComplex.homologyMap
        (restrictionCorestrictionCochains A T) n =
      HomologicalComplex.homologyMap
        (H.index • 𝟙 (inhomogeneousCochains A)) n := by
  let e := inhomogeneousResolutionLinearHomCochainIso A
  let b := restrictionCorestrictionResolutionCochains A T
  let s := H.index • 𝟙
    ((HomologicalComplex.linearHomCochainComplexFunctor
      k (Rep k G) A).obj
        (Opposite.op (Rep.barResolution k G).complex))
  have hSquare : restrictionCorestrictionCochains A T ≫ e.hom =
      e.hom ≫ b :=
    restrictionCorestrictionCochains_comp_resolutionLinearHomIso_hom A T
  have hBar : HomologicalComplex.homologyMap b n =
      HomologicalComplex.homologyMap s n :=
    (restrictionCorestrictionResolutionCochainsHomotopy
      (H := H) A T).homologyMap_eq n
  have hScalar :
      (H.index • 𝟙 (inhomogeneousCochains A)) ≫ e.hom =
        e.hom ≫ s := by
    dsimp only [s]
    rw [Preadditive.nsmul_comp, Preadditive.comp_nsmul]
    simp only [Category.id_comp, Category.comp_id]
  apply (cancel_mono (HomologicalComplex.homologyMap e.hom n)).mp
  calc
    HomologicalComplex.homologyMap
          (restrictionCorestrictionCochains A T) n ≫
        HomologicalComplex.homologyMap e.hom n =
      HomologicalComplex.homologyMap
        (restrictionCorestrictionCochains A T ≫ e.hom) n := by
          rw [HomologicalComplex.homologyMap_comp]
    _ = HomologicalComplex.homologyMap (e.hom ≫ b) n := by
      rw [hSquare]
    _ = HomologicalComplex.homologyMap e.hom n ≫
        HomologicalComplex.homologyMap b n := by
      rw [HomologicalComplex.homologyMap_comp]
    _ = HomologicalComplex.homologyMap e.hom n ≫
        HomologicalComplex.homologyMap s n := by rw [hBar]
    _ = HomologicalComplex.homologyMap (e.hom ≫ s) n := by
      rw [HomologicalComplex.homologyMap_comp]
    _ = HomologicalComplex.homologyMap
        ((H.index • 𝟙 (inhomogeneousCochains A)) ≫ e.hom) n := by
      rw [hScalar]
    _ = HomologicalComplex.homologyMap
          (H.index • 𝟙 (inhomogeneousCochains A)) n ≫
        HomologicalComplex.homologyMap e.hom n := by
      rw [HomologicalComplex.homologyMap_comp]

set_option backward.isDefEq.respectTransparency false in
/-- In every degree, chosen-transversal corestriction after restriction is
multiplication by the subgroup index. -/
theorem corestrictionOfRightTransversal_restriction
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex] (n : ℕ) :
    groupCohomology.map (Subgroup.subtype H)
        (𝟙 (Rep.res (Subgroup.subtype H) A)) n ≫
      corestrictionOfRightTransversal A T n =
        H.index • 𝟙 (groupCohomology A n) := by
  change HomologicalComplex.homologyMap
      (groupCohomology.cochainsMap (Subgroup.subtype H)
        (𝟙 (Rep.res (Subgroup.subtype H) A))) n ≫
    HomologicalComplex.homologyMap (corestrictionCochains A T) n = _
  rw [← HomologicalComplex.homologyMap_comp]
  change HomologicalComplex.homologyMap
      (restrictionCorestrictionCochains A T) n = _
  change HomologicalComplex.homologyMap
      (restrictionCorestrictionCochains A T) n =
    H.index • 𝟙 ((inhomogeneousCochains A).homology n)
  rw [homologyMap_restrictionCorestrictionCochains]
  change (HomologicalComplex.homologyFunctor (ModuleCat k)
    (ComplexShape.up ℕ) n).map (H.index • 𝟙 (inhomogeneousCochains A)) = _
  rw [CategoryTheory.Functor.map_nsmul, CategoryTheory.Functor.map_id]
  rfl

/-- Elementwise arbitrary-degree restriction--corestriction formula. -/
theorem corestrictionOfRightTransversal_restriction_apply
    (A : Rep k G) (T : H.RightTransversal) [H.FiniteIndex] (n : ℕ)
    (x : groupCohomology A n) :
    corestrictionOfRightTransversal A T n
        (groupCohomology.map (Subgroup.subtype H)
          (𝟙 (Rep.res (Subgroup.subtype H) A)) n x) =
      (H.index : k) • x := by
  have h := ConcreteCategory.congr_hom
    (corestrictionOfRightTransversal_restriction A T n) x
  change corestrictionOfRightTransversal A T n
      (groupCohomology.map (Subgroup.subtype H)
        (𝟙 (Rep.res (Subgroup.subtype H) A)) n x) =
    H.index • x at h
  simpa only [Nat.cast_smul_eq_nsmul] using h

/-- Restriction to a finite-index subgroup is injective in every degree when
the subgroup index is a unit in the coefficient ring. -/
theorem restriction_injective_of_isUnit_index
    (A : Rep k G) [H.FiniteIndex] (n : ℕ)
    (hindex : IsUnit (H.index : k)) :
    Function.Injective
      (groupCohomology.map (Subgroup.subtype H)
        (𝟙 (Rep.res (Subgroup.subtype H) A)) n) := by
  let T : H.RightTransversal := default
  intro x y hxy
  apply hindex.smul_left_cancel.mp
  rw [← corestrictionOfRightTransversal_restriction_apply A T n x,
    ← corestrictionOfRightTransversal_restriction_apply A T n y, hxy]

end groupCohomology
