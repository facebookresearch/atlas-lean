/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.Embedding.RestrictionExtendAdjunction
public import MathlibExt.Algebra.Homology.Embedding.NatInitialInterval
public import MathlibExt.Algebra.Homology.Embedding.StupidTruncMap
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Finite cotruncations of nonnegative cochain complexes

Cotruncation at `q` retains degrees `0` through `q`. The restriction and
extension adjunction gives the projection. Restricting a larger
cotruncation to a smaller interval gives transitions forming a natural
inverse system.

Below the cutoff, the projection retains all three terms of the homology
row and induces a cohomology isomorphism. The top degree is excluded from
this comparison.
-/

@[expose] public section
noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape.NatInitialInterval

attribute [local implicit_reducible] HomologicalComplex.homologyFunctor

universe u v

namespace CochainComplex

variable {C : Type u} [Category.{v} C]

section Maps

variable [HasZeroMorphisms C] [HasZeroObject C]

/-- Finite cotruncation retaining the initial cochain degrees. -/
abbrev finiteCotruncation (K : CochainComplex C ℕ) (q : ℕ) : CochainComplex C ℕ :=
  K.stupidTrunc (upEmbedding q)

/-- Coordinate chart in a retained degree. -/
def finiteCotruncationXIso (K : CochainComplex C ℕ) (q n : ℕ) (hn : n ≤ q) :
    (K.finiteCotruncation q).X n ≅ K.X n :=
  K.stupidTruncXIso (upEmbedding q) (i := ⟨n, by omega⟩) rfl

/-- Finite cotruncation vanishes outside its interval. -/
theorem finiteCotruncation_isZero (K : CochainComplex C ℕ) (q n : ℕ) (hn : q < n) :
    IsZero ((K.finiteCotruncation q).X n) :=
  K.isZero_stupidTrunc_X (upEmbedding q) n (by
    intro i hi
    have hmem : n ∈ Set.range (upEmbedding q).f := ⟨i, hi⟩
    have := (upEmbedding_range q n).1 hmem
    omega)

/-- Retained differentials expressed through coordinate charts. -/
theorem finiteCotruncation_d (K : CochainComplex C ℕ) (q i j : ℕ)
    (hi : i ≤ q) (hj : j ≤ q) :
    (K.finiteCotruncation q).d i j =
      (K.finiteCotruncationXIso q i hi).hom ≫ K.d i j ≫
        (K.finiteCotruncationXIso q j hj).inv :=
  K.stupidTrunc_d_eq (upEmbedding q) (i := ⟨i, by omega⟩) (j := ⟨j, by omega⟩) rfl rfl

/-- Map of finite cotruncations induced by a cochain map. -/
abbrev finiteCotruncationMap {K L : CochainComplex C ℕ} (f : K ⟶ L) (q : ℕ) :
    K.finiteCotruncation q ⟶ L.finiteCotruncation q :=
  HomologicalComplex.stupidTruncMap f (upEmbedding q)

/-- Finite-cotruncation functor. -/
def finiteCotruncationFunctor (q : ℕ) : CochainComplex C ℕ ⥤ CochainComplex C ℕ :=
  (upEmbedding q).stupidTruncFunctor C

/-- Projection given by the restriction and extension adjunction unit. -/
abbrev πFiniteCotruncation (K : CochainComplex C ℕ) (q : ℕ) :
    K ⟶ K.finiteCotruncation q := K.πStupidTrunc (upEmbedding q)

theorem πFiniteCotruncation_f (K : CochainComplex C ℕ) (q n : ℕ) (hn : n ≤ q) :
    (K.πFiniteCotruncation q).f n = (K.finiteCotruncationXIso q n hn).inv :=
  K.πStupidTrunc_f (upEmbedding q) (p := ⟨n, by omega⟩) rfl

theorem πFiniteCotruncation_f_zero (K : CochainComplex C ℕ) (q n : ℕ) (hn : q < n) :
    (K.πFiniteCotruncation q).f n = 0 :=
  (K.finiteCotruncation_isZero q n hn).eq_of_tgt _ _

/-- Naturality of the finite-cotruncation projection. -/
@[reassoc]
theorem πFiniteCotruncation_naturality {K L : CochainComplex C ℕ} (f : K ⟶ L) (q : ℕ) :
    f ≫ L.πFiniteCotruncation q =
      K.πFiniteCotruncation q ≫ finiteCotruncationMap f q :=
  HomologicalComplex.πStupidTrunc_naturality (upEmbedding q) f

/-- Identification of a larger cotruncation on a smaller interval with the restricted complex. -/
def finiteCotruncationRestrictionIso (K : CochainComplex C ℕ) {p q : ℕ} (hpq : p ≤ q) :
    (K.finiteCotruncation q).restriction (upEmbedding p) ≅
      K.restriction (upEmbedding p) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => K.finiteCotruncationXIso q i.val
      ((Nat.le_of_lt_succ i.isLt).trans hpq))
    (by
      intro i j hij
      have hi : i.val ≤ q := (Nat.le_of_lt_succ i.isLt).trans hpq
      have hj : j.val ≤ q := (Nat.le_of_lt_succ j.isLt).trans hpq
      change (K.finiteCotruncationXIso q i.val hi).hom ≫ K.d i.val j.val =
        (K.finiteCotruncation q).d i.val j.val ≫
          (K.finiteCotruncationXIso q j.val hj).hom
      rw [finiteCotruncation_d K q i.val j.val hi hj]
      let a := (K.finiteCotruncationXIso q i.val hi).hom
      let d := K.d i.val j.val
      let e := K.finiteCotruncationXIso q j.val hj
      change a ≫ d = (a ≫ d ≫ e.inv) ≫ e.hom
      exact ((Category.assoc a (d ≫ e.inv) e.hom).trans
        ((congrArg (fun z => a ≫ z) (Category.assoc d e.inv e.hom)).trans
          ((congrArg (fun z => a ≫ d ≫ z) e.inv_hom_id).trans
            (congrArg (fun z => a ≫ z) (Category.comp_id d))))).symm)

/-- Transition map from a larger cotruncation to a smaller one. -/
def finiteCotruncationTransition (K : CochainComplex C ℕ) {p q : ℕ} (hpq : p ≤ q) :
    K.finiteCotruncation q ⟶ K.finiteCotruncation p :=
  (upEmbedding p).liftExtend (K.finiteCotruncationRestrictionIso hpq).hom
    ((upEmbedding p).hasLift_of_isTruncLE _)

/-- Transitions preserve coordinates in the smaller interval. -/
theorem finiteCotruncationTransition_f (K : CochainComplex C ℕ) {p q : ℕ}
    (hpq : p ≤ q) (n : ℕ) (hn : n ≤ p) :
    (K.finiteCotruncationTransition hpq).f n =
      (K.finiteCotruncationXIso q n (hn.trans hpq)).hom ≫
        (K.finiteCotruncationXIso p n hn).inv := by
  let i : Fin (p + 1) := ⟨n, by omega⟩
  let eQ := K.finiteCotruncationXIso q n (hn.trans hpq)
  let eP := K.finiteCotruncationXIso p n hn
  have hf := (upEmbedding p).liftExtend_f
    (K.finiteCotruncationRestrictionIso hpq).hom
    ((upEmbedding p).hasLift_of_isTruncLE _) (i := i) rfl
  have hR : ((K.finiteCotruncation q).restrictionXIso (upEmbedding p) (i := i) rfl).inv =
      𝟙 ((K.finiteCotruncation q).X n) := rfl
  have hComponent : (K.finiteCotruncationRestrictionIso hpq).hom.f i = eQ.hom := rfl
  have hValue : (K.finiteCotruncationTransition hpq).f n =
      eQ.hom ≫ ((K.restriction (upEmbedding p)).extendXIso (upEmbedding p) (i := i) rfl).inv :=
    hf.trans ((congrArg₂ (fun z w => z ≫ w ≫
      ((K.restriction (upEmbedding p)).extendXIso (upEmbedding p) (i := i) rfl).inv)
        hR hComponent).trans (Category.id_comp _))
  have hCoordinate : eP.inv =
      ((K.restriction (upEmbedding p)).extendXIso (upEmbedding p) (i := i) rfl).inv := by
    unfold eP finiteCotruncationXIso HomologicalComplex.stupidTruncXIso HomologicalComplex.stupidTrunc
    rw [Iso.trans_inv]
    exact Category.id_comp _
  exact hValue.trans (congrArg (fun z => eQ.hom ≫ z) hCoordinate.symm)

theorem finiteCotruncationTransition_f_zero (K : CochainComplex C ℕ) {p q : ℕ}
    (hpq : p ≤ q) (n : ℕ) (hn : p < n) :
    (K.finiteCotruncationTransition hpq).f n = 0 :=
  (K.finiteCotruncation_isZero p n hn).eq_of_tgt _ _

/-- A transition factors the cotruncation projections. -/
@[reassoc]
theorem πFiniteCotruncation_transition (K : CochainComplex C ℕ)
    {p q : ℕ} (hpq : p ≤ q) :
    K.πFiniteCotruncation q ≫ K.finiteCotruncationTransition hpq =
      K.πFiniteCotruncation p := by
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hn : n ≤ p
  · rw [HomologicalComplex.comp_f, πFiniteCotruncation_f K q n (hn.trans hpq),
      finiteCotruncationTransition_f K hpq n hn, πFiniteCotruncation_f K p n hn]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
  · exact (K.finiteCotruncation_isZero p n (by omega)).eq_of_tgt _ _

/-- Projection factorization determines the transition uniquely. -/
theorem finiteCotruncationTransition_unique (K : CochainComplex C ℕ)
    {p q : ℕ} (hpq : p ≤ q)
    (f : K.finiteCotruncation q ⟶ K.finiteCotruncation p)
    (hf : K.πFiniteCotruncation q ≫ f = K.πFiniteCotruncation p) :
    f = K.finiteCotruncationTransition hpq := by
  apply (cancel_epi (K.πFiniteCotruncation q)).1
  exact hf.trans (K.πFiniteCotruncation_transition hpq).symm

@[simp]
theorem finiteCotruncationTransition_refl (K : CochainComplex C ℕ) (p : ℕ) :
    K.finiteCotruncationTransition (le_refl p) = 𝟙 _ := by
  apply (cancel_epi (K.πFiniteCotruncation p)).1
  rw [πFiniteCotruncation_transition, Category.comp_id]

/-- Transitions compose in inverse-system order. -/
@[reassoc]
theorem finiteCotruncationTransition_comp (K : CochainComplex C ℕ)
    {p q r : ℕ} (hpq : p ≤ q) (hqr : q ≤ r) :
    K.finiteCotruncationTransition hqr ≫ K.finiteCotruncationTransition hpq =
      K.finiteCotruncationTransition (hpq.trans hqr) := by
  apply (cancel_epi (K.πFiniteCotruncation r)).1
  simp only [← Category.assoc, πFiniteCotruncation_transition]

/-- Naturality of finite-cotruncation transitions. -/
@[reassoc]
theorem finiteCotruncationTransition_naturality {K L : CochainComplex C ℕ}
    (f : K ⟶ L) {p q : ℕ} (hpq : p ≤ q) :
    finiteCotruncationMap f q ≫ L.finiteCotruncationTransition hpq =
      K.finiteCotruncationTransition hpq ≫ finiteCotruncationMap f p := by
  apply (cancel_epi (K.πFiniteCotruncation q)).1
  rw [← Category.assoc, ← πFiniteCotruncation_naturality, Category.assoc,
    πFiniteCotruncation_transition, ← Category.assoc,
    πFiniteCotruncation_transition, ← πFiniteCotruncation_naturality]

/-- Finite cotruncations as an inverse system. -/
def finiteCotruncationSystem (K : CochainComplex C ℕ) :
    ℕᵒᵖ ⥤ CochainComplex C ℕ where
  obj q := K.finiteCotruncation q.unop
  map f := K.finiteCotruncationTransition (leOfHom f.unop)
  map_id q := finiteCotruncationTransition_refl K q.unop
  map_comp f g := (finiteCotruncationTransition_comp K
    (leOfHom g.unop) (leOfHom f.unop)).symm

/-- Natural projection from the whole complex to the finite-cotruncation system. -/
def πFiniteCotruncationSystem (K : CochainComplex C ℕ) :
    (Functor.const ℕᵒᵖ).obj K ⟶ finiteCotruncationSystem K where
  app q := K.πFiniteCotruncation q.unop
  naturality := by
    intro p q f
    change 𝟙 K ≫ K.πFiniteCotruncation q.unop =
      K.πFiniteCotruncation p.unop ≫ K.finiteCotruncationTransition (leOfHom f.unop)
    exact (Category.id_comp _).trans
      (K.πFiniteCotruncation_transition (leOfHom f.unop)).symm

/-- Universal map into a target extended from a finite interval. -/
def finiteRestrictionExtendHomEquiv (q : ℕ) (K : CochainComplex C ℕ)
    (L : HomologicalComplex C (upShape q)) :
    (K.restriction (upEmbedding q) ⟶ L) ≃ (K ⟶ L.extend (upEmbedding q)) :=
  (upEmbedding q).restrictionExtendHomEquiv K L

end Maps

section Homology

variable [Abelian C]

/-- Below the cutoff, the projection is invertible on the three homology-row terms. -/
theorem πFiniteCotruncation_quasiIsoAt (K : CochainComplex C ℕ)
    (q n : ℕ) (hn : n < q) : QuasiIsoAt (K.πFiniteCotruncation q) n := by
  have hnq : n ≤ q := Nat.le_of_lt hn
  have hnext : (ComplexShape.up ℕ).next n ≤ q := by
    rw [(ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel n (n + 1) from rfl)]
    omega
  have hprev : (ComplexShape.up ℕ).prev n ≤ q := by
    cases n with
    | zero => simp only [CochainComplex.prev_nat_zero]; omega
    | succ n => simp only [CochainComplex.prev_nat_succ]; omega
  let f := K.πFiniteCotruncation q
  letI : IsIso (f.f ((ComplexShape.up ℕ).prev n)) := by
    change IsIso ((K.πFiniteCotruncation q).f ((ComplexShape.up ℕ).prev n))
    rw [πFiniteCotruncation_f K q _ hprev]
    infer_instance
  letI : IsIso (f.f n) := by
    change IsIso ((K.πFiniteCotruncation q).f n)
    rw [πFiniteCotruncation_f K q n hnq]
    infer_instance
  letI : IsIso (f.f ((ComplexShape.up ℕ).next n)) := by
    change IsIso ((K.πFiniteCotruncation q).f ((ComplexShape.up ℕ).next n))
    rw [πFiniteCotruncation_f K q _ hnext]
    infer_instance
  rw [quasiIsoAt_iff]
  let φ := (HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℕ) n).map f
  letI : Epi φ.τ₁ := inferInstanceAs (Epi (f.f ((ComplexShape.up ℕ).prev n)))
  letI : IsIso φ.τ₂ := inferInstanceAs (IsIso (f.f n))
  letI : Mono φ.τ₃ := inferInstanceAs (Mono (f.f ((ComplexShape.up ℕ).next n)))
  exact ShortComplex.quasiIso_of_epi_of_isIso_of_mono φ

/-- The projection induces cohomology isomorphisms below the cutoff. -/
def finiteCotruncationHomologyIso (K : CochainComplex C ℕ) (q n : ℕ) (hn : n < q) :
    K.homology n ≅ (K.finiteCotruncation q).homology n := by
  letI : QuasiIsoAt (K.πFiniteCotruncation q) n := K.πFiniteCotruncation_quasiIsoAt q n hn
  exact isoOfQuasiIsoAt (K.πFiniteCotruncation q) n

@[simp]
theorem finiteCotruncationHomologyIso_hom (K : CochainComplex C ℕ)
    (q n : ℕ) (hn : n < q) :
    (K.finiteCotruncationHomologyIso q n hn).hom =
      HomologicalComplex.homologyMap (K.πFiniteCotruncation q) n := rfl

/-- Naturality of the cotruncation homology comparison. -/
@[reassoc]
theorem finiteCotruncationHomologyIso_naturality {K L : CochainComplex C ℕ}
    (f : K ⟶ L) (q n : ℕ) (hn : n < q) :
    HomologicalComplex.homologyMap f n ≫ (L.finiteCotruncationHomologyIso q n hn).hom =
      (K.finiteCotruncationHomologyIso q n hn).hom ≫
        HomologicalComplex.homologyMap (finiteCotruncationMap f q) n := by
  have h := congrArg (fun g => HomologicalComplex.homologyMap g n)
    (πFiniteCotruncation_naturality f q)
  simpa only [finiteCotruncationHomologyIso_hom, HomologicalComplex.homologyMap_comp] using h

end Homology

end CochainComplex
