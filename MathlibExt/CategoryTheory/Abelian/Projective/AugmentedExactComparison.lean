/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChainComplexAugmentation
public import MathlibExt.CategoryTheory.Abelian.Injective.AugmentedExactComparisonExistence
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.CategoryTheory.EpiMono

/-!
# Projective chain sources and exact augmented targets

In an abelian category `C`, a chain complex with projective terms maps
to any augmented complex whose augmentation is a quasi-isomorphism.
Such maps extending the same resolved-object map are homotopic. The
target terms need not be projective.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v u' v'

namespace ChainComplex

variable {C : Type u} [Category.{v} C] [Abelian C]
  {X : C} {K : ChainComplex C ℕ}

/-- In an abelian category `C`, an augmentation `ε : K → X[0]`
of a natural-index chain complex gives the opposite coaugmentation
`op X[0] → K.op` in `Cᵒᵖ`, with the same degree-zero map
after taking its opposite. -/
def opCoaugmentation (ε : K ⟶ (single₀ C).obj X) :
    (CochainComplex.single₀ Cᵒᵖ).obj (Opposite.op X) ⟶ K.op :=
  (CochainComplex.fromSingle₀Equiv K.op (Opposite.op X)).symm
    ⟨(ε.f 0).op, by
      change (ε.f 0).op ≫ (K.d 1 0).op = 0
      rw [← op_comp]
      have hε : K.d 1 0 ≫ ε.f 0 = 0 := by
        rw [← ε.comm 1 0, HomologicalComplex.single_obj_d, comp_zero]
      rw [hε, op_zero]⟩

/-- For a chain augmentation `ε : K → X[0]` in an abelian category
`C`, its opposite coaugmentation into `K.op` has degree-zero
component `(ε₀).op`. -/
theorem opCoaugmentation_f_zero (ε : K ⟶ (single₀ C).obj X) :
    (opCoaugmentation ε).f 0 = (ε.f 0).op :=
  CochainComplex.fromSingle₀Equiv_symm_apply_f_zero _ _

/-- For a chain augmentation `ε : K → X[0]` in an abelian category
`C`, the opposite coaugmentation has zero component in every
positive degree `n+1`, since the single-object source vanishes there. -/
theorem opCoaugmentation_f_succ (ε : K ⟶ (single₀ C).obj X) (n : ℕ) :
    (opCoaugmentation ε).f (n + 1) = 0 :=
  (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0
    (Opposite.op X) (n + 1) (by omega)).eq_of_src _ _

/-- In an abelian category `C`, if `ε : K → X[0]` is a
quasi-isomorphism of natural-index chain complexes, each positive
row `K^(n+2) → K^(n+1) → K^n` is exact. -/
theorem exact_succ_of_augmentedQuasiIso
    (ε : K ⟶ (single₀ C).obj X) [QuasiIso ε] (n : ℕ) :
    (ShortComplex.mk (K.d (n + 2) (n + 1)) (K.d (n + 1) n)
      (K.d_comp_d (n + 2) (n + 1) n)).Exact := by
  have hK : K.ExactAt (n + 1) :=
    (exactAt_iff_of_quasiIsoAt ε (n + 1)).mpr (exactAt_succ_single_obj X n)
  exact (HomologicalComplex.exactAt_iff' K (n + 2) (n + 1) n
    (by simp) (by simp)).mp hK

/-- In an abelian category `C`, a quasi-isomorphism `ε : K → X[0]`
gives an exact opposite augmentation row
`op X → (K.op)⁰ → (K.op)¹` in `Cᵒᵖ`. -/
theorem opCoaugmentation_exact_zero
    (ε : K ⟶ (single₀ C).obj X) [QuasiIso ε] :
    (ShortComplex.mk ((opCoaugmentation ε).f 0) (K.op.d 0 1)
      (by rw [(opCoaugmentation ε).comm 0 1,
        HomologicalComplex.single_obj_d, zero_comp])).Exact := by
  let S : ShortComplex C := ShortComplex.mk (K.d 1 0) (ε.f 0)
    (by rw [← ε.comm 1 0, HomologicalComplex.single_obj_d, comp_zero])
  let T : ShortComplex Cᵒᵖ := ShortComplex.mk
    ((opCoaugmentation ε).f 0) (K.op.d 0 1)
    (by rw [(opCoaugmentation ε).comm 0 1, HomologicalComplex.single_obj_d, zero_comp])
  let e : T ≅ S.op := ShortComplex.isoMk
    (Iso.refl (Opposite.op X))
    (Iso.refl (Opposite.op (K.X 0)))
    (Iso.refl (Opposite.op (K.X 1)))
    (by
      change 𝟙 _ ≫ (ε.f 0).op = (opCoaugmentation ε).f 0 ≫ 𝟙 _
      exact (Category.id_comp _).trans
        ((opCoaugmentation_f_zero ε).symm.trans (Category.comp_id _).symm))
    (by
      change 𝟙 _ ≫ (K.d 1 0).op = (K.d 1 0).op ≫ 𝟙 _
      exact (Category.id_comp _).trans (Category.comp_id _).symm)
  exact (ShortComplex.exact_iff_of_iso e).mpr (exact_augmentation ε).op

/-- In an abelian category `C`, a quasi-isomorphism `ε : K → X[0]`
gives exact cochain rows `(K.op)^n → (K.op)^(n+1) →
(K.op)^(n+2)` in every nonnegative degree. -/
theorem opCoaugmentation_exact_succ
    (ε : K ⟶ (single₀ C).obj X) [QuasiIso ε] (n : ℕ) :
    (ShortComplex.mk (K.op.d n (n + 1)) (K.op.d (n + 1) (n + 2))
      (K.op.d_comp_d n (n + 1) (n + 2))).Exact :=
  (exact_succ_of_augmentedQuasiIso ε n).op

end ChainComplex

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]
  {X Y : C} {P Q : ChainComplex C ℕ}

/-- In an abelian category `C`, let `P → X[0]` have projective
terms and let `ρ : Q → Y[0]` be a quasi-isomorphism. Every
`f : X → Y` extends to a chain map `a : P → Q` with
`a ≫ ρ = ε ≫ single₀(f)`. -/
theorem exists_projectiveAugmentedExactComparison
    (ε : P ⟶ (ChainComplex.single₀ C).obj X)
    (ρ : Q ⟶ (ChainComplex.single₀ C).obj Y) [QuasiIso ρ]
    (hP : ∀ n : ℕ, Projective (P.X n)) (f : X ⟶ Y) :
    ∃ a : P ⟶ Q, a ≫ ρ = ε ≫ (ChainComplex.single₀ C).map f := by
  let ι := ChainComplex.opCoaugmentation ρ
  let κ := ChainComplex.opCoaugmentation ε
  letI : Epi (ρ.f 0) := ChainComplex.epi_augmentation_f_zero ρ
  letI : Mono (ι.f 0) := by
    have hm : Mono ((ρ.f 0).op) := @CategoryTheory.op_mono_of_epi C _
      (((ChainComplex.single₀ C).obj Y).X 0) (Q.X 0) (ρ.f 0)
      (ChainComplex.epi_augmentation_f_zero ρ)
    exact (ChainComplex.opCoaugmentation_f_zero ρ).symm ▸ hm
  have hI : ∀ n : ℕ, Injective (P.op.X n) := by
    intro n
    letI : Projective (P.X n) := hP n
    change Injective (Opposite.op (P.X n))
    infer_instance
  obtain ⟨a, ha⟩ := exists_augmentedExactComparison ι κ
    (ChainComplex.opCoaugmentation_exact_zero ρ)
    (ChainComplex.opCoaugmentation_exact_succ ρ) hI f.op
  let b : P ⟶ Q := ((HomologicalComplex.opInverse C (ComplexShape.down ℕ)).map a).unop
  refine ⟨b, ?_⟩
  apply HomologicalComplex.hom_ext
  intro n
  cases n with
  | zero =>
    let m := (CochainComplex.single₀ Cᵒᵖ).map f.op
    have hL : @Eq (Opposite.op Y ⟶ P.op.X 0)
        ((ι ≫ a).f 0) ((ρ.f 0).op ≫ a.f 0) :=
      (HomologicalComplex.comp_f ι a 0).trans
        (congrArg (fun z => z ≫ a.f 0) (ChainComplex.opCoaugmentation_f_zero ρ))
    have hR : @Eq (Opposite.op Y ⟶ P.op.X 0)
        ((m ≫ κ).f 0) (f.op ≫ (ε.f 0).op) :=
      (HomologicalComplex.comp_f m κ 0).trans
        (congrArg₂ (fun z w => z ≫ w)
          (CochainComplex.single₀_map_f_zero f.op) (ChainComplex.opCoaugmentation_f_zero ε))
    have hCore : @Eq (Opposite.op Y ⟶ P.op.X 0)
        ((ρ.f 0).op ≫ a.f 0) (f.op ≫ (ε.f 0).op) :=
      hL.symm.trans ((HomologicalComplex.congr_hom ha 0).trans hR)
    have hU := congrArg Quiver.Hom.unop hCore
    have hUL : @Eq (P.X 0 ⟶ Y)
        (((ρ.f 0).op ≫ a.f 0).unop) (b.f 0 ≫ ρ.f 0) :=
      (CategoryTheory.unop_comp (f := (ρ.f 0).op) (g := a.f 0)).trans
        (congrArg₂ (fun z w => z ≫ w)
          (show (a.f 0).unop = b.f 0 from rfl)
          (show ((ρ.f 0).op).unop = ρ.f 0 from rfl))
    have hUR : @Eq (P.X 0 ⟶ Y)
        ((f.op ≫ (ε.f 0).op).unop) (ε.f 0 ≫ f) :=
      (CategoryTheory.unop_comp (f := f.op) (g := (ε.f 0).op)).trans
        (congrArg₂ (fun z w => z ≫ w)
          (show ((ε.f 0).op).unop = ε.f 0 from rfl) (show f.op.unop = f from rfl))
    have hOriginalL : @Eq (P.X 0 ⟶ Y) ((b ≫ ρ).f 0) (b.f 0 ≫ ρ.f 0) := rfl
    have hOriginalR : @Eq (P.X 0 ⟶ Y)
        ((ε ≫ (ChainComplex.single₀ C).map f).f 0) (ε.f 0 ≫ f) :=
      (HomologicalComplex.comp_f ε ((ChainComplex.single₀ C).map f) 0).trans
        (congrArg (fun z => ε.f 0 ≫ z) (ChainComplex.single₀_map_f_zero f))
    exact hOriginalL.trans (hUL.symm.trans (hU.trans (hUR.trans hOriginalR.symm)))
  | succ n =>
    exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0 Y
      (n + 1) (by omega)).eq_of_tgt _ _

/-- In an abelian category `C`, let `P` have projective terms and
`ρ : Q → Y[0]` be a quasi-isomorphism. Maps `a,b : P → Q`
with `a ≫ ρ = b ≫ ρ` are chain-homotopic. -/
def projectiveAugmentedExactComparisonHomotopy
    (ρ : Q ⟶ (ChainComplex.single₀ C).obj Y) [QuasiIso ρ]
    (hP : ∀ n : ℕ, Projective (P.X n)) (a b : P ⟶ Q)
    (hab : a ≫ ρ = b ≫ ρ) : Homotopy a b := by
  let ι := ChainComplex.opCoaugmentation ρ
  let A := (HomologicalComplex.opFunctor C (ComplexShape.down ℕ)).map a.op
  let B := (HomologicalComplex.opFunctor C (ComplexShape.down ℕ)).map b.op
  have hI : ∀ n : ℕ, Injective (P.op.X n) := by
    intro n
    letI : Projective (P.X n) := hP n
    change Injective (Opposite.op (P.X n))
    infer_instance
  have hAB : ι ≫ A = ι ≫ B := by
    apply HomologicalComplex.hom_ext
    intro n
    cases n with
    | zero =>
      have hA0 : A.f 0 = (a.f 0).op := rfl
      have hB0 : B.f 0 = (b.f 0).op := rfl
      have hL : @Eq (Opposite.op Y ⟶ P.op.X 0)
          ((ι ≫ A).f 0) ((ρ.f 0).op ≫ (a.f 0).op) :=
        (HomologicalComplex.comp_f ι A 0).trans
          (congrArg₂ (fun z w => z ≫ w) (ChainComplex.opCoaugmentation_f_zero ρ) hA0)
      have hR : @Eq (Opposite.op Y ⟶ P.op.X 0)
          ((ι ≫ B).f 0) ((ρ.f 0).op ≫ (b.f 0).op) :=
        (HomologicalComplex.comp_f ι B 0).trans
          (congrArg₂ (fun z w => z ≫ w) (ChainComplex.opCoaugmentation_f_zero ρ) hB0)
      have h0 : a.f 0 ≫ ρ.f 0 = b.f 0 ≫ ρ.f 0 :=
        HomologicalComplex.congr_hom hab 0
      have hop : @Eq (Opposite.op Y ⟶ P.op.X 0)
          ((ρ.f 0).op ≫ (a.f 0).op) ((ρ.f 0).op ≫ (b.f 0).op) :=
        (CategoryTheory.op_comp (f := a.f 0) (g := ρ.f 0)).symm.trans
          ((congrArg Quiver.Hom.op h0).trans
            (CategoryTheory.op_comp (f := b.f 0) (g := ρ.f 0)))
      exact hL.trans (hop.trans hR.symm)
    | succ n =>
      exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℕ) 0
        (Opposite.op Y) (n + 1) (by omega)).eq_of_src _ _
  let h := augmentedExactComparisonHomotopy ι
    (ChainComplex.opCoaugmentation_exact_zero ρ)
    (ChainComplex.opCoaugmentation_exact_succ ρ) hI A B hAB
  exact h.unop

/-- For abelian `C`, `D` and additive `F : C → D`, let `P`
have projective terms and let `ρ : Q → Y[0]` be a
quasi-isomorphism. If `a,b : P → Q` agree after `ρ`, then
`F(a)` and `F(b)` induce equal maps on homology in every
natural-number degree. -/
theorem projectiveAugmentedExactComparison_homologyMap_eq
    {D : Type u'} [Category.{v'} D] [Abelian D] (F : C ⥤ D) [F.Additive]
    (ρ : Q ⟶ (ChainComplex.single₀ C).obj Y) [QuasiIso ρ]
    (hP : ∀ n : ℕ, Projective (P.X n)) (a b : P ⟶ Q)
    (hab : a ≫ ρ = b ≫ ρ) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map a) n =
      HomologicalComplex.homologyMap
        ((F.mapHomologicalComplex (ComplexShape.down ℕ)).map b) n :=
  (F.mapHomotopy (projectiveAugmentedExactComparisonHomotopy ρ hP a b hab)).homologyMap_eq n

end CategoryTheory
