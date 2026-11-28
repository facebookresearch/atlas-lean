/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Authors: Avocado
-/
module

public import MathlibExt.Algebra.Homology.CochainGradedPairingHomologyHeterogeneous
public import MathlibExt.Algebra.Homology.LinearHomCochainPairing

/-!
# Units and comparison maps for Hom cohomology pairings

Work over a commutative ring R with nonnegative complexes of R-modules and
coefficient modules in carrier universe u. For a chain map ε : K → R[0]
and an R-linear coefficient map e : R → A, the cochain e ∘ ε₀ is a cocycle
in Hom_R(K; A)^0 and defines a map R → Z⁰(Hom_R(K; A)).

Associativity and unit identities for graded cochain pairings descend to
cohomology through specified comparison maps on terms, cycles, and cohomology.
These maps must commute with the cycle inclusions and cycle-to-cohomology
projections. Given these two compatibility equations, a cochain associativity
or unit equation implies the corresponding cohomology equation, including
comparisons between distinct output complexes.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite

universe u


namespace HomologicalComplex

variable (R : Type u) [CommRing R]

/-- For a commutative ring R, a nonnegative cochain complex K of R-modules,
and equal degrees p = q, this is the canonical isomorphism Zᵖ(K) ≅ Zᑫ(K).
It transports cycles along the given identification of degrees. -/
noncomputable def cochainCyclesIsoOfEq
    (K : CochainComplex (ModuleCat.{u} R) ℕ) {p q : ℕ} (h : p = q) :
    K.cycles p ≅ K.cycles q := by
  subst q
  exact Iso.refl _

/-- For a commutative ring R, a nonnegative cochain complex K of R-modules,
and equal degrees p = q, this is the canonical isomorphism Hᵖ(K) ≅ Hᑫ(K).
It transports cohomology classes along the given identification of degrees. -/
noncomputable def cochainHomologyIsoOfEq
    (K : CochainComplex (ModuleCat.{u} R) ℕ) {p q : ℕ} (h : p = q) :
    K.homology p ≅ K.homology q := by
  subst q
  exact Iso.refl _

@[reassoc]
theorem cochainCyclesIsoOfEq_hom_iCycles
    (K : CochainComplex (ModuleCat.{u} R) ℕ) {p q : ℕ} (h : p = q) :
    (cochainCyclesIsoOfEq R K h).hom ≫ K.iCycles q =
      K.iCycles p ≫ (K.XIsoOfEq h).hom := by
  subst q
  simp [cochainCyclesIsoOfEq]

@[reassoc]
theorem cochainHomologyπ_comp_cochainHomologyIsoOfEq_hom
    (K : CochainComplex (ModuleCat.{u} R) ℕ) {p q : ℕ} (h : p = q) :
    K.homologyπ p ≫ (cochainHomologyIsoOfEq R K h).hom =
      (cochainCyclesIsoOfEq R K h).hom ≫ K.homologyπ q := by
  subst q
  simp [cochainCyclesIsoOfEq, cochainHomologyIsoOfEq]

noncomputable def cochainMapXOfEq
    {K L : CochainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L)
    {p q : ℕ} (h : p = q) : K.X p ⟶ L.X q :=
  f.f p ≫ (L.XIsoOfEq h).hom

noncomputable def cochainCyclesMapOfEq
    {K L : CochainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L)
    {p q : ℕ} (h : p = q) : K.cycles p ⟶ L.cycles q :=
  K.cyclesMap f p ≫ (cochainCyclesIsoOfEq R L h).hom

noncomputable def cochainHomologyMapOfEq
    {K L : CochainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L)
    {p q : ℕ} (h : p = q) : K.homology p ⟶ L.homology q :=
  K.homologyMap f p ≫ (cochainHomologyIsoOfEq R L h).hom

@[reassoc]
theorem cochainCyclesMapOfEq_i
    {K L : CochainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L)
    {p q : ℕ} (h : p = q) :
    cochainCyclesMapOfEq R f h ≫ L.iCycles q =
      K.iCycles p ≫ cochainMapXOfEq R f h := by
  unfold cochainCyclesMapOfEq cochainMapXOfEq
  rw [Category.assoc, cochainCyclesIsoOfEq_hom_iCycles]
  rw [← Category.assoc, cyclesMap_i]
  rw [Category.assoc]

@[reassoc]
theorem cochainHomologyπ_comp_cochainHomologyMapOfEq
    {K L : CochainComplex (ModuleCat.{u} R) ℕ} (f : K ⟶ L)
    {p q : ℕ} (h : p = q) :
    K.homologyπ p ≫ cochainHomologyMapOfEq R f h =
      cochainCyclesMapOfEq R f h ≫ L.homologyπ q := by
  unfold cochainHomologyMapOfEq cochainCyclesMapOfEq
  slice_lhs 1 2 => rw [homologyπ_naturality]
  slice_lhs 2 3 =>
    rw [cochainHomologyπ_comp_cochainHomologyIsoOfEq_hom]
  exact (Category.assoc _ _ _).symm

/-- Let R be a commutative ring, K a nonnegative chain complex of
R-modules, ε : K → R[0] a chain map, A an R-module, and e : R → A
an R-linear map. The resulting degree-zero Hom cochain is
K₀ → R → A, namely e ∘ ε₀ after identifying the degree-zero term of
the tensor unit R[0] with R. -/
noncomputable def linearHomCochainUnitOfCounit
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (ε : K ⟶ 𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ))
    (A : ModuleCat.{u} R) (e : 𝟙_ (ModuleCat.{u} R) ⟶ A) :
    ((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj (op K)).X 0 :=
  ε.f 0 ≫
    (singleObjXSelf (ComplexShape.down ℕ) 0
      (𝟙_ (ModuleCat.{u} R))).hom ≫ e

@[simp]
theorem linearHomCochainUnitOfCounit_d
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (ε : K ⟶ 𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ))
    (A : ModuleCat.{u} R) (e : 𝟙_ (ModuleCat.{u} R) ⟶ A) :
    (((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj (op K)).d 0 1).hom
        (linearHomCochainUnitOfCounit R K ε A e) = 0 := by
  change K.d 1 0 ≫ ε.f 0 ≫
      (singleObjXSelf (ComplexShape.down ℕ) 0
        (𝟙_ (ModuleCat.{u} R))).hom ≫ e = 0
  have hd : K.d 1 0 ≫ ε.f 0 = 0 := by
    calc
      _ = ε.f 1 ≫
          (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ)).d 1 0 :=
        (ε.comm 1 0).symm
      _ = _ := by
        rw [show (𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ)).d 1 0 = 0 by
          change ((single (ModuleCat.{u} R) (ComplexShape.down ℕ) 0).obj
            (𝟙_ (ModuleCat.{u} R))).d 1 0 = 0
          apply single_obj_d]
        simp
  rw [← Category.assoc, hd]
  simp

/-- Let R be a commutative ring, K a nonnegative chain complex of
R-modules, ε : K → R[0] a chain map, A an R-module, and e : R → A
an R-linear map. This map R → Hom_R(K₀, A) sends r to
r • (e ∘ ε₀), using the identification R[0]₀ ≅ R.
In particular, it sends 1 to the cochain determined by ε and e. -/
noncomputable def linearHomCochainUnitOfCounitHom
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (ε : K ⟶ 𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ))
    (A : ModuleCat.{u} R) (e : 𝟙_ (ModuleCat.{u} R) ⟶ A) :
    𝟙_ (ModuleCat.{u} R) ⟶
      ((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj (op K)).X 0 :=
  ModuleCat.ofHom
    (LinearMap.toSpanSingleton R _ (linearHomCochainUnitOfCounit R K ε A e))

@[reassoc (attr := simp)]
theorem linearHomCochainUnitOfCounitHom_d
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (ε : K ⟶ 𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ))
    (A : ModuleCat.{u} R) (e : 𝟙_ (ModuleCat.{u} R) ⟶ A) :
    linearHomCochainUnitOfCounitHom R K ε A e ≫
      ((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj (op K)).d 0 1 = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change r • ((((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj
    (op K)).d 0 1).hom (linearHomCochainUnitOfCounit R K ε A e)) = 0
  rw [linearHomCochainUnitOfCounit_d]
  exact smul_zero r

/-- Let R be a commutative ring, K a nonnegative chain complex of
R-modules, ε : K → R[0] a chain map, A an R-module, and e : R → A
an R-linear map. The cochain e ∘ ε₀ is closed because ε₀ ∘ d_K = 0.
This is the map R → Z⁰(Hom_R(K; A)) sending 1 to that cocycle. -/
noncomputable def linearHomCochainUnitOfCounitCycles
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (ε : K ⟶ 𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ))
    (A : ModuleCat.{u} R) (e : 𝟙_ (ModuleCat.{u} R) ⟶ A) :
    𝟙_ (ModuleCat.{u} R) ⟶
      ((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj (op K)).cycles 0 :=
  ((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj (op K)).liftCycles
    (linearHomCochainUnitOfCounitHom R K ε A e)
    1 (by simp) (linearHomCochainUnitOfCounitHom_d R K ε A e)

@[reassoc (attr := simp)]
theorem linearHomCochainUnitOfCounitCycles_i
    (K : ChainComplex (ModuleCat.{u} R) ℕ)
    (ε : K ⟶ 𝟙_ (ChainComplex (ModuleCat.{u} R) ℕ))
    (A : ModuleCat.{u} R) (e : 𝟙_ (ModuleCat.{u} R) ⟶ A) :
    linearHomCochainUnitOfCounitCycles R K ε A e ≫
        ((linearHomCochainComplexFunctor R (ModuleCat.{u} R) A).obj
          (op K)).iCycles 0 =
      linearHomCochainUnitOfCounitHom R K ε A e := by
  apply HomologicalComplex.liftCycles_i

end HomologicalComplex

namespace HomologicalComplex.CochainGradedPairing

variable (R : Type u) [CommRing R]

/-- Let R be a commutative ring and let P₁₂, Pₗ, P₂₃, Pᵣ be graded
pairings of nonnegative cochain complexes of R-modules, with left output L
and right output R′ in degrees (p + q) + r and p + (q + r).
Suppose comparison maps c_X, c_Z, c_H between these output terms, cycles,
and cohomology satisfy i_R′ ∘ c_Z = c_X ∘ i_L and
c_H ∘ π_L = π_R′ ∘ c_Z. If
c_X ∘ Pₗ ∘ (P₁₂ ⊗ id) = Pᵣ ∘ (id ⊗ P₂₃) ∘ α on cochains, then
the identical associativity equation holds on cohomology with c_H and
the associator of the cohomology modules. -/
theorem pairHomology_associativity_of_pair
    {K₁ K₂ K₃ K₁₂ K₂₃ L R' : CochainComplex (ModuleCat.{u} R) ℕ}
    (P₁₂ : CochainGradedPairing K₁ K₂ K₁₂)
    (Pₗ : CochainGradedPairing K₁₂ K₃ L)
    (P₂₃ : CochainGradedPairing K₂ K₃ K₂₃)
    (Pᵣ : CochainGradedPairing K₁ K₂₃ R')
    (p q r : ℕ)
    (comparisonX : L.X ((p + q) + r) ⟶ R'.X (p + (q + r)))
    (comparisonCycles : L.cycles ((p + q) + r) ⟶ R'.cycles (p + (q + r)))
    (comparisonHomology : L.homology ((p + q) + r) ⟶
      R'.homology (p + (q + r)))
    (comparisonCycles_i : comparisonCycles ≫ R'.iCycles (p + (q + r)) =
      L.iCycles ((p + q) + r) ≫ comparisonX)
    (comparison_π : L.homologyπ ((p + q) + r) ≫ comparisonHomology =
      comparisonCycles ≫ R'.homologyπ (p + (q + r)))
    (hpair :
      (P₁₂.pair p q ⊗ₘ 𝟙 (K₃.X r)) ≫
          Pₗ.pair (p + q) r ≫ comparisonX =
        (α_ (K₁.X p) (K₂.X q) (K₃.X r)).hom ≫
          (𝟙 (K₁.X p) ⊗ₘ P₂₃.pair q r) ≫
          Pᵣ.pair p (q + r)) :
    (P₁₂.pairHomology p q ⊗ₘ 𝟙 (K₃.homology r)) ≫
        Pₗ.pairHomology (p + q) r ≫ comparisonHomology =
      (α_ (K₁.homology p) (K₂.homology q) (K₃.homology r)).hom ≫
        (𝟙 (K₁.homology p) ⊗ₘ P₂₃.pairHomology q r) ≫
        Pᵣ.pairHomology p (q + r) := by
  apply pairHomology_associativity R P₁₂ Pₗ P₂₃ Pᵣ p q r comparisonHomology
  rw [comparison_π]
  simp only [← Category.assoc]
  congr 1
  apply (cancel_mono (R'.iCycles (p + (q + r)))).1
  simp only [Category.assoc]
  rw [comparisonCycles_i]
  simp only [← Category.assoc]
  slice_lhs 2 3 => rw [Pₗ.pairCycles_i]
  slice_rhs 3 4 => rw [Pᵣ.pairCycles_i]
  slice_lhs 1 2 => rw [MonoidalCategory.tensorHom_comp_tensorHom]
  slice_rhs 2 3 => rw [MonoidalCategory.tensorHom_comp_tensorHom]
  rw [P₁₂.pairCycles_i, P₂₃.pairCycles_i]
  simp only [Category.assoc]
  simp only [Category.id_comp]
  have hleftTensor :
      (((K₁.iCycles p ⊗ₘ K₂.iCycles q) ≫ P₁₂.pair p q) ⊗ₘ K₃.iCycles r) =
        (((K₁.iCycles p ⊗ₘ K₂.iCycles q) ⊗ₘ K₃.iCycles r) ≫
          (P₁₂.pair p q ⊗ₘ 𝟙 (K₃.X r))) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp
  have hrightTensor :
      (K₁.iCycles p ⊗ₘ
          ((K₂.iCycles q ⊗ₘ K₃.iCycles r) ≫ P₂₃.pair q r)) =
        (K₁.iCycles p ⊗ₘ (K₂.iCycles q ⊗ₘ K₃.iCycles r)) ≫
          (𝟙 (K₁.X p) ⊗ₘ P₂₃.pair q r) := by
    rw [MonoidalCategory.tensorHom_comp_tensorHom]
    simp
  rw [hleftTensor, hrightTensor]
  simp only [Category.assoc]
  rw [← MonoidalCategory.associator_naturality_assoc]
  rw [hpair]

/-- Let R be a commutative ring, P a graded pairing of nonnegative
cochain complexes U and K into L, q ∈ ℕ, and u : R → Z⁰(U) a chosen
cocycle map. Suppose c_X : L_(0+q) → K_q, c_Z : Z⁰⁺ᑫ(L) → Zᑫ(K),
and c_H : H⁰⁺ᑫ(L) → Hᑫ(K) satisfy i_K ∘ c_Z = c_X ∘ i_L and
c_H ∘ π_L = π_K ∘ c_Z. If pairing with i_U ∘ u followed by c_X
equals the left tensor unitor on K_q, then pairing with the class π_U ∘ u
followed by c_H equals the left tensor unitor on Hᑫ(K). -/
theorem pairHomology_left_unit_of_pair
    {U K L : CochainComplex (ModuleCat.{u} R) ℕ}
    (P : CochainGradedPairing U K L) (q : ℕ)
    (unitCycles : 𝟙_ (ModuleCat.{u} R) ⟶ U.cycles 0)
    (comparisonX : L.X (0 + q) ⟶ K.X q)
    (comparisonCycles : L.cycles (0 + q) ⟶ K.cycles q)
    (comparisonHomology : L.homology (0 + q) ⟶ K.homology q)
    (comparisonCycles_i : comparisonCycles ≫ K.iCycles q =
      L.iCycles (0 + q) ≫ comparisonX)
    (comparison_π : L.homologyπ (0 + q) ≫ comparisonHomology =
      comparisonCycles ≫ K.homologyπ q)
    (hpair :
      ((unitCycles ≫ U.iCycles 0) ▷ K.X q) ≫
          P.pair 0 q ≫ comparisonX =
        (λ_ (K.X q)).hom) :
    ((unitCycles ≫ U.homologyπ 0) ▷ K.homology q) ≫
        P.pairHomology 0 q ≫ comparisonHomology =
      (λ_ (K.homology q)).hom := by
  apply pairHomology_left_unit R P q unitCycles comparisonHomology
  rw [comparison_π]
  have hcycles :
      (unitCycles ▷ K.cycles q) ≫ P.pairCycles 0 q ≫ comparisonCycles =
        (λ_ (K.cycles q)).hom := by
    apply (cancel_mono (K.iCycles q)).1
    simp only [Category.assoc]
    rw [comparisonCycles_i]
    slice_lhs 2 3 => rw [P.pairCycles_i]
    simp only [Category.assoc]
    rw [MonoidalCategory.whiskerRight_comp_tensorHom_assoc]
    have htensor :
        (unitCycles ≫ U.iCycles 0 ⊗ₘ K.iCycles q) =
          (((𝟙_ (ModuleCat.{u} R)) ◁ K.iCycles q) ≫
            ((unitCycles ≫ U.iCycles 0) ▷ K.X q)) := by
      rw [MonoidalCategory.tensorHom_def]
      exact (MonoidalCategory.whisker_exchange
        (unitCycles ≫ U.iCycles 0) (K.iCycles q)).symm
    rw [htensor]
    simp only [Category.assoc]
    rw [hpair]
    exact MonoidalCategory.leftUnitor_naturality (K.iCycles q)
  slice_lhs 1 3 => rw [hcycles]

/-- Let R be a commutative ring, P a graded pairing of nonnegative
cochain complexes K and U into L, p ∈ ℕ, and u : R → Z⁰(U) a chosen
cocycle map. Suppose c_X : L_(p+0) → K_p, c_Z : Zᵖ⁺⁰(L) → Zᵖ(K),
and c_H : Hᵖ⁺⁰(L) → Hᵖ(K) satisfy i_K ∘ c_Z = c_X ∘ i_L and
c_H ∘ π_L = π_K ∘ c_Z. If pairing on the right with i_U ∘ u followed
by c_X equals the right tensor unitor on K_p, then pairing on the right
with π_U ∘ u followed by c_H equals the right tensor unitor on Hᵖ(K). -/
theorem pairHomology_right_unit_of_pair
    {K U L : CochainComplex (ModuleCat.{u} R) ℕ}
    (P : CochainGradedPairing K U L) (p : ℕ)
    (unitCycles : 𝟙_ (ModuleCat.{u} R) ⟶ U.cycles 0)
    (comparisonX : L.X (p + 0) ⟶ K.X p)
    (comparisonCycles : L.cycles (p + 0) ⟶ K.cycles p)
    (comparisonHomology : L.homology (p + 0) ⟶ K.homology p)
    (comparisonCycles_i : comparisonCycles ≫ K.iCycles p =
      L.iCycles (p + 0) ≫ comparisonX)
    (comparison_π : L.homologyπ (p + 0) ≫ comparisonHomology =
      comparisonCycles ≫ K.homologyπ p)
    (hpair :
      (K.X p ◁ (unitCycles ≫ U.iCycles 0)) ≫
          P.pair p 0 ≫ comparisonX =
        (ρ_ (K.X p)).hom) :
    (K.homology p ◁ (unitCycles ≫ U.homologyπ 0)) ≫
        P.pairHomology p 0 ≫ comparisonHomology =
      (ρ_ (K.homology p)).hom := by
  apply pairHomology_right_unit R P p unitCycles comparisonHomology
  rw [comparison_π]
  have hcycles :
      (K.cycles p ◁ unitCycles) ≫ P.pairCycles p 0 ≫ comparisonCycles =
        (ρ_ (K.cycles p)).hom := by
    apply (cancel_mono (K.iCycles p)).1
    simp only [Category.assoc]
    rw [comparisonCycles_i]
    slice_lhs 2 3 => rw [P.pairCycles_i]
    simp only [Category.assoc]
    rw [MonoidalCategory.whiskerLeft_comp_tensorHom_assoc]
    have htensor :
        (K.iCycles p ⊗ₘ (unitCycles ≫ U.iCycles 0)) =
          ((K.iCycles p ▷ (𝟙_ (ModuleCat.{u} R))) ≫
            (K.X p ◁ (unitCycles ≫ U.iCycles 0))) := by
      exact MonoidalCategory.tensorHom_def _ _
    rw [htensor]
    simp only [Category.assoc]
    rw [hpair]
    exact MonoidalCategory.rightUnitor_naturality (K.iCycles p)
  slice_lhs 1 3 => rw [hcycles]

end HomologicalComplex.CochainGradedPairing

namespace HomologicalComplex

variable (R : Type u) [CommRing R]

noncomputable local instance linearHomHeterogeneousChainComplexMonoidalCategory :
    MonoidalCategory (ChainComplex (ModuleCat.{u} R) ℕ) :=
  HomologicalComplex.monoidalCategory (ModuleCat.{u} R) (ComplexShape.down ℕ)

noncomputable abbrev linearHomCochainComplex
    (K : ChainComplex (ModuleCat.{u} R) ℕ) (M : ModuleCat.{u} R) :
    CochainComplex (ModuleCat.{u} R) ℕ :=
  (linearHomCochainComplexFunctor R (ModuleCat.{u} R) M).obj (op K)

noncomputable def linearHomCochainComparison
    {K L : ChainComplex (ModuleCat.{u} R) ℕ}
    {M N : ModuleCat.{u} R} (f : K ⟶ L) (a : M ⟶ N) :
    linearHomCochainComplex R L M ⟶ linearHomCochainComplex R K N :=
  (linearHomCochainComplexFunctor R (ModuleCat.{u} R) M).map f.op ≫
    ((linearHomCochainComplexBifunctor R (ModuleCat.{u} R)).map a).app (op K)


end HomologicalComplex
