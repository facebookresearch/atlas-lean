/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
-- Author: @toskua, Avocado
module

-- BACKPORT: Full-file backport of
-- `Mathlib/AlgebraicTopology/SimplicialSet/KanComplex/PtSimplexEquiv.lean`
-- from PR leanprover-community/mathlib4#42435 head
-- `e09070f786c9fc0a688e6239d71230b618b045ff`, blob
-- `7ea85363e456723ba4461cb98f3f0e8ac75b8e0f`.
-- Copied surface: 26-declaration nondeprecated packet (Homotopy abbrev,
-- RelStruct symm/trans/succ/ofSucc/relStruct₀, RelStruct₀ refl/symm/trans/
-- relStruct, Homotopy equiv₀/δ_whiskerRight_h_eq_const/
-- δ_ι_h_eq_const_of_gt/δ_ι_h_eq_const_of_lt/src/tgt/src_zero/src_succ/
-- tgt_last/ρ/relStruct₀, SSet.PtSimplex.cases_one/cases_last,
-- RelStruct₀.homotopy, MulStruct.unique/unique'); includes auxiliary
-- `cases_one`/`cases_last`.
-- Historical preparation used Lean 4.33 and Mathlib pin `db584cd`.
-- The retained import/proof adaptations below are checked on Lean 4.35.0
-- and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`:
-- FundamentalGroupoid resolves to the local MathlibExt provider;
-- ProdStdSimplexOne uses ProdStdSimplexOneCompat; MonoidalCompat supplies
-- the retained leftUnitor/rightUnitor lemmas. MulStruct is canonical
-- `Mathlib.AlgebraicTopology.SimplicialSet.KanComplex.MulStruct`, and
-- `Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes` is imported.
-- No boundary.hom_ext_tensor* helper declarations are defined/copied.
-- The retained inline boundary proof steps are: ordinary →
-- `apply boundary.hom_ext; intro i`, left tensor →
-- `MonoidalClosed.curry_injective` + `boundary.hom_ext` +
-- `curry_natural_left`, right tensor →
-- `rw [← cancel_epi (β_ _ _).hom]` then left-tensor via
-- `curry_injective`/`boundary.hom_ext`/`prodStdSimplex₁.hom_ext`/
-- `curry_natural_left`, ∂Δ[0] → ext over impossible simplex + simp at
-- membership proof.
-- Deletion rule: delete this MathlibExt module and switch imports to
-- Mathlib once pin contains file.
-- See BACKPORTS.md, BLUEPRINT_1_YEAR.md, and shared orchestration policy.

public import Mathlib.AlgebraicTopology.SimplicialSet.KanComplex.MulStruct
public import MathlibExt.AlgebraicTopology.SimplicialSet.KanComplex.FundamentalGroupoid
public import MathlibExt.AlgebraicTopology.SimplicialSet.ProdStdSimplexOneCompat
public import MathlibExt.AlgebraicTopology.SimplicialSet.MonoidalCompat
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

/-!
# Equivalence relations between pointed simplices


-/

@[expose] public section

universe u

open HomotopicalAlgebra CategoryTheory Simplicial MonoidalCategory

namespace SSet.PtSimplex

variable {X : SSet.{u}} {n : ℕ} {x : X _⦋0⦌}

/-- Given `p` and `q` in `X.PtSimplex n x`, this is the type of homotopies between
`p` and `q`. These homotopies are given by morphisms `Δ[n] ⊗ Δ[1] ⟶ X`.
(This contrasts with `RelStruct` or `RelStruct₀` which only involve the more
basic data of a morphism `Δ[n + 1] ⟶ X`. See `SSet.PtSimplex.Homotopy.relStruct₀`
and `SSet.PtSimplex.RelStruct₀.homotopy` for a connection between these
two notions for Kan complexes.) -/
abbrev Homotopy (p q : X.PtSimplex n x) : Type u := RelativeMorphism.Homotopy p q

namespace RelStruct

open MulStruct

variable [KanComplex X]

/-- The symmetry of `RelStruct`. -/
@[no_expose]
noncomputable def symm {p q : X.PtSimplex n x} {i : Fin (n + 1)} (h : RelStruct p q i) :
    RelStruct q p i := by
  obtain _ | n  := n
  · obtain rfl : i = 0 := by fin_cases i; rfl
    exact RelStruct₀.equiv₀.symm (RelStruct₀.equiv₀ h).inv
  · apply Nonempty.some
    obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
    · exact ⟨relStructCastSuccEquivMulStruct.symm
        (oneMulEqSymm ((relStructCastSuccEquivMulStruct (i := 0) h)))⟩
    · exact ⟨relStructSuccEquivMulStruct.symm
        (mulOneEqSymm (relStructSuccEquivMulStruct h))⟩

/-- The transivitiy of `RelStruct`. -/
@[no_expose]
noncomputable def trans {p q r : X.PtSimplex n x} {i : Fin (n + 1)} (h : RelStruct p q i)
    (h' : RelStruct q r i) : RelStruct p r i := by
  obtain _ | n := n
  · obtain rfl : i = 0 := by fin_cases i; rfl
    exact RelStruct₀.equiv₀.symm ((RelStruct₀.equiv₀ h').comp (RelStruct₀.equiv₀ h))
  · apply Nonempty.some
    obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
    · exact ⟨relStructCastSuccEquivMulStruct.symm
        (oneMulEqTrans
        ((relStructCastSuccEquivMulStruct (i := 0) h))
        ((relStructCastSuccEquivMulStruct (i := 0) h')))⟩
    · exact ⟨relStructSuccEquivMulStruct.symm
        (mulOneEqTrans (relStructSuccEquivMulStruct h')
        (relStructSuccEquivMulStruct h))⟩

/-- A `RelStruct p q i.succ` structure deduced from a `RelStruct p q i.castSucc` structure. -/
@[no_expose]
noncomputable def succ {p q : X.PtSimplex n x} {i : Fin n} (h : RelStruct p q i.castSucc) :
    RelStruct p q i.succ := by
  obtain _ | n := n
  · exfalso
    fin_cases i
  · exact relStructSuccEquivMulStruct.symm
      (mulOneEqOfOneMulEq (relStructCastSuccEquivMulStruct h.symm))

/-- A `RelStruct p q i.castSucc` structure deduced from a `RelStruct p q i.succ` structure. -/
@[no_expose]
noncomputable def ofSucc {p q : X.PtSimplex n x} {i : Fin n} (h : RelStruct p q i.succ) :
    RelStruct p q i.castSucc := by
  obtain _ | n := n
  · exfalso
    fin_cases i
  · exact relStructCastSuccEquivMulStruct.symm
      ((oneMulEqOfMulOneEq (relStructSuccEquivMulStruct h.symm)))

/-- A `RelStruct₀ p q` structure deduced from a `RelStruct p q i` structure. -/
@[no_expose]
noncomputable def relStruct₀ {p q : X.PtSimplex n x} {i : Fin (n + 1)} (h : RelStruct p q i) :
    RelStruct₀ p q := by
  induction i using Fin.induction  with
  | zero => exact h
  | succ i hi => exact hi h.ofSucc

end RelStruct

namespace RelStruct₀

/-- `RelStruct₀` is reflexive. -/
abbrev refl (p : X.PtSimplex n x) : RelStruct₀ p p := RelStruct.refl _ _

variable [KanComplex X]

/-- `RelStruct₀` is symmetric. -/
noncomputable abbrev symm {p q : X.PtSimplex n x} (h : RelStruct₀ p q) : RelStruct₀ q p :=
  RelStruct.symm h

/-- `RelStruct₀` is transitive. -/
noncomputable abbrev trans {p q r : X.PtSimplex n x} (h₁ : RelStruct₀ p q) (h₂ : RelStruct₀ q r) :
    RelStruct₀ p r :=
  RelStruct.trans h₁ h₂

/-- A `Relstruct p q i` structure deduced from a `RelStruct₀ p q` structure. -/
noncomputable def relStruct {p q : X.PtSimplex n x}
    (h : RelStruct₀ p q) (i : Fin (n + 1)) : RelStruct p q i := by
  obtain _ | n := n
  · obtain rfl : i = 0 := by aesop
    exact h
  · induction i using Fin.induction  with
    | zero => exact h
    | succ i hi => exact hi.succ

end RelStruct₀

namespace Homotopy

/-- In dimension zero, the homotopy relation on `SSet.PtSimplex` is given by edges. -/
def equiv₀ {p q : X.PtSimplex 0 x} :
    Homotopy p q ≃ Edge ((equiv₀ x) p) ((equiv₀ x) q) where
  toFun h :=
    Edge.mk (yonedaEquiv ((stdSimplex.leftUnitor _).inv ≫ h.h))
      (by simp [← stdSimplex.yonedaEquiv_δ_comp, ← ι₀_stdSimplex_zero_assoc])
      (by simp [← stdSimplex.yonedaEquiv_δ_comp, ← ι₁_stdSimplex_zero_assoc])
  invFun e :=
    { h := (stdSimplex.leftUnitor _).hom ≫ yonedaEquiv.symm e.edge
      h₀ := by simp [ι₀_stdSimplex_zero_assoc, stdSimplex.δ_comp_yonedaEquiv_symm]
      h₁ := by simp [ι₁_stdSimplex_zero_assoc, stdSimplex.δ_comp_yonedaEquiv_symm]
      rel := by
        ext q ⟨⟨_, hq⟩, _⟩
        simp at hq }
  left_inv _ := by cat_disch
  right_inv _ := by cat_disch

@[reassoc (attr := simp)]
lemma δ_whiskerRight_h_eq_const {p q : X.PtSimplex (n + 1) x} (h : Homotopy p q)
    (k : Fin (n + 2)) :
    stdSimplex.δ k ▷ Δ[1] ≫ h.h = const x := by
  simpa only [← comp_whiskerRight_assoc, boundary.ι_ι, Subcomplex.ofSimplex_ι,
     comp_const] using boundary.ι k ▷ _ ≫= h.rel

@[reassoc]
lemma δ_ι_h_eq_const_of_gt {p q : X.PtSimplex (n + 1) x} (h : Homotopy p q)
    (i : Fin (n + 3)) (j : Fin (n + 2))
    (hij : j.succ < i := by grind) :
    stdSimplex.δ i ≫ prodStdSimplex₁.ι j ≫ h.h = const x := by
  rw [prodStdSimplex₁.δ_ι_of_gt_assoc .., δ_whiskerRight_h_eq_const, comp_const]

@[reassoc]
lemma δ_ι_h_eq_const_of_lt {p q : X.PtSimplex (n + 1) x} (h : Homotopy p q)
    (i : Fin (n + 3)) (j : Fin (n + 2))
    (hij : i < j.castSucc := by grind) :
    stdSimplex.δ i ≫ prodStdSimplex₁.ι j ≫ h.h = const x := by
  rw [prodStdSimplex₁.δ_ι_of_lt_assoc .., δ_whiskerRight_h_eq_const, comp_const]

namespace relStruct₀

/-! The following are auxiliary definitions towards the definition
`SSet.PtSimplex.Homotopy.relStruct₀`. If `p` anq `q` are elements
in `X.PtSimplex (n + 1) x` and `h : Homotopy p q`, we have a
morphism `h.h : Δ[n + 1] ⊗ Δ[1] ⟶ X`. As `Δ[n + 1] ⊗ Δ[1]`
is "covered" by `n + 2` simplices of dimension `n + 2`, we
consider the restriction of `h.h` to each of these `n + 2`-simplices:
this is the definition `ρ` below, which gives a finite sequence
of `RelStruct` structures (with source and target points given by the definitions
`src` and `tgt`). By "composing" these and using the symmetry, we
obtain a map `Homotopy → RelStruct₀`.
-/

variable {p q : X.PtSimplex (n + 1) x} (h : Homotopy p q)

/-- Intermediate elements in `X.PtSimplex (n + 1) x` that are given by
a homotopy between elements in `X.PtSimplex (n + 1) x`. -/
@[simps]
noncomputable def src (i : Fin (n + 2)) : X.PtSimplex (n + 1) x where
  map := stdSimplex.δ i.castSucc ≫ prodStdSimplex₁.ι i ≫ h.h
  comm := by
    apply boundary.hom_ext
    intro j
    simp only [boundary.ι_ι_assoc, Subcomplex.ofSimplex_ι, comp_const]
    by_cases! hij : i < j
    · rw [← stdSimplex.δ_comp_δ_assoc hij.le, h.δ_ι_h_eq_const_of_gt .., comp_const]
    · obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
      · simp [prodStdSimplex₁.δ_ι_zero_assoc]
      · obtain hij | rfl := hij.lt_or_eq
        · dsimp
          rw [stdSimplex.δ_comp_δ_assoc (by grind), h.δ_ι_h_eq_const_of_lt .., comp_const]
        · dsimp
          rw [prodStdSimplex₁.δ_succ_castSucc_ι_succ_assoc,
            dsimp% stdSimplex.δ_comp_δ_self_assoc (i := i.succ),
            h.δ_ι_h_eq_const_of_gt .., comp_const]

@[simps, inherit_doc src]
noncomputable def tgt (i : Fin (n + 2)) : X.PtSimplex (n + 1) x where
  map := stdSimplex.δ i.succ ≫ prodStdSimplex₁.ι i ≫ h.h
  comm := by
    apply boundary.hom_ext
    intro j
    simp only [boundary.ι_ι_assoc, Subcomplex.ofSimplex_ι, comp_const]
    by_cases! hij : i < j
    · obtain ⟨i, rfl⟩ := i.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hij)
      rw [← dsimp% stdSimplex.δ_comp_δ_assoc (i := i.succ) (by grind),
        h.δ_ι_h_eq_const_of_gt .., comp_const]
    · rw [stdSimplex.δ_comp_δ_assoc hij]
      obtain hij | rfl := hij.lt_or_eq
      · rw [h.δ_ι_h_eq_const_of_lt .., comp_const]
      · obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ
        · simp [prodStdSimplex₁.δ_ι_zero_assoc]
        · dsimp
          rw [prodStdSimplex₁.δ_succ_castSucc_ι_succ_assoc,
            dsimp% stdSimplex.δ_comp_δ_self_assoc (i := j.succ),
            h.δ_ι_h_eq_const_of_gt .., comp_const]

@[simp]
lemma src_zero : src h 0 = q := by
  ext : 1
  simp [prodStdSimplex₁.δ_ι_zero_assoc]

lemma src_succ (i : Fin (n + 1)) :
    src h i.succ = tgt h i.castSucc := by
  ext : 1
  simp [prodStdSimplex₁.δ_succ_castSucc_ι_succ_assoc]

@[simp]
lemma tgt_last :
    tgt h (Fin.last _) = p := by
  ext : 1
  simp [prodStdSimplex₁.δ_ι_last_assoc]

/-- Given a homotopy `h : Homotopy p q` between relements in `X.PtSimplex (n + 1) x`,
and `i : Fin (n + 2)`, this is a `RelStruct` structure obtained by considering
the restriction of the map `h.h : Δ[n + 1] ⊗ Δ[1] ⟶ X` to the `i`th
nondegenerate `(n + 2)`-simplex of `Δ[n + 1] ⊗ Δ[1]`. -/
@[simps]
noncomputable def ρ (i : Fin (n + 2)) : RelStruct (src h i) (tgt h i) i where
  map := prodStdSimplex₁.ι i ≫ h.h
  δ_castSucc_map := rfl
  δ_succ_map := rfl
  δ_map_of_gt j hij := by rw [h.δ_ι_h_eq_const_of_gt ..]
  δ_map_of_lt j hij := by rw [h.δ_ι_h_eq_const_of_lt ..]

end relStruct₀

open relStruct₀ in
/-- Given `p` and `q` in `X.PtSimplex n x`, this is a choice of map
`Homotopy p q → RelStruct₀ p q`. -/
@[no_expose]
noncomputable def relStruct₀ [KanComplex X] {p q : X.PtSimplex n x} (h : Homotopy p q) :
    RelStruct₀ p q := by
  obtain _ | n := n
  · exact RelStruct₀.equiv₀.symm (Homotopy.equiv₀ h).inv
  · have (i : Fin (n + 2)) : RelStruct₀ q (tgt h i) := by
      induction i using Fin.induction with
      | zero => simpa using ρ h 0
      | succ i hi => exact hi.trans (by simpa [src_succ] using (ρ h i.succ).relStruct₀)
    simpa using (this (Fin.last _)).symm

end Homotopy

-- to be moved
@[simp, grind =] theorem cases_one {n : ℕ} {motive : Fin (n + 2) → Sort _} {zero succ} :
  Fin.cases (motive := motive) zero succ 1 = succ 0 := rfl

-- to be moved
@[simp, grind =] theorem cases_last {n : ℕ} {motive : Fin (n + 2) → Sort _} {zero succ} :
  Fin.cases (motive := motive) zero succ (Fin.last _) = succ (Fin.last _) := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Given `p` and `q` in `X.PtSimplex n x`, this is a choice of map
`RelStruct₀ p q → Homotopy p q`. -/
noncomputable def RelStruct₀.homotopy [KanComplex X]
    {p q : X.PtSimplex n x} (h : RelStruct₀ p q) : Homotopy p q :=
  Nonempty.some (by
    obtain ⟨s, hs⟩ := prodStdSimplex₁.exists_desc
      (Fin.cases h.symm.map (fun i ↦ stdSimplex.σ i.succ ≫ p.map)) (fun i ↦ by
        obtain _ | n := n
        · fin_cases i
        · obtain rfl | ⟨i, rfl⟩ := i.eq_zero_or_eq_succ
          · simp [dsimp% SSet.stdSimplex.δ_comp_σ_self_assoc
                    (n := n + 1) (i := 1),
              dsimp% h.symm.δ_succ_map, SSet.PtSimplex.cases_one]
          · simp [dsimp% SSet.stdSimplex.{u}.δ_comp_σ_self_assoc
                    (i := i.succ.succ),
              SSet.stdSimplex.{u}.δ_comp_σ_succ_assoc
                    (i := i.castSucc.succ)])
    exact ⟨{
      h := s
      h₀ := by
        rw [← dsimp% h.symm.δ_succ_map,
          ← SSet.prodStdSimplex₁.δ_ι_last_assoc, hs]
        obtain _ | n := n
        · simp
        · simp [dsimp% SSet.stdSimplex.δ_comp_σ_succ_assoc
                  (i := Fin.last (n + 1)),
            dsimp% h.symm.δ_succ_map, SSet.PtSimplex.cases_last]
      h₁ := by
        simpa [dsimp% h.symm.δ_castSucc_map,
          prodStdSimplex₁.δ_ι_zero_assoc] using stdSimplex.δ 0 ≫= hs 0
      rel := by
        obtain _ | n := n
        · ext q ⟨⟨_, hq⟩, _⟩
          simp at hq
        · rw [← cancel_epi (β_ _ _).hom]
          apply MonoidalClosed.curry_injective
          apply boundary.hom_ext
          intro i
          simp only [← MonoidalClosed.curry_natural_left]
          apply congrArg MonoidalClosed.curry
          rw [← cancel_epi (β_ _ _).hom]
          simp only [BraidedCategory.braiding_naturality_right_assoc,
            SymmetricCategory.symmetry_assoc]
          simp only [← MonoidalCategory.comp_whiskerRight_assoc, boundary.ι_ι,
            Subcomplex.ofSimplex_ι, comp_const]
          apply prodStdSimplex₁.hom_ext
          intro j
          by_cases! hij : i ≤ j.castSucc
          · simp [prodStdSimplex₁.ι_δ_whiskerRight_of_le_assoc _ _ hij, hs,
              stdSimplex.δ_comp_σ_of_le_assoc hij]
          · simp only [prodStdSimplex₁.ι_δ_whiskerRight_of_gt_assoc _ _ hij, hs]
            obtain rfl | ⟨j, rfl⟩ := j.eq_zero_or_eq_succ
            · simp [h.symm.δ_map_of_gt i.succ (by grind)]
            · simp [dsimp% stdSimplex.δ_comp_σ_of_gt_assoc hij]
    }⟩)

/-- Up to homotopy (expressed here using `PtSimplex.RelStruct₀`),
the multiplication on the homotopy groups of Kan complexes (which is done in the file
`Mathlib/AlgebraicTopology/SimplicialSet/KanComplex/HomotopyGroup.lean`) is well defined. -/
@[no_expose]
noncomputable def MulStruct.unique
    [KanComplex X] {p₀₁ p₁₂ p₀₂ p₀₁' p₁₂' p₀₂' : X.PtSimplex (n + 1) x} {i : Fin (n + 1)}
    (h : MulStruct p₀₁ p₁₂ p₀₂ i)
    (h' : MulStruct p₀₁' p₁₂' p₀₂' i)
    (h₀₁ : RelStruct₀ p₀₁ p₀₁') (h₁₂ : RelStruct₀ p₁₂ p₁₂') :
    RelStruct₀ p₀₂ p₀₂' :=
  RelStruct.relStruct₀
    (relStructSuccEquivMulStruct.symm
      (assoc h' (relStructSuccEquivMulStruct (h₁₂.relStruct i.succ))
        (assoc (relStructSuccEquivMulStruct (h₀₁.symm.relStruct i.succ)) (oneMul p₁₂ i) h)))

/-- From a `MulStruct p₀₁ p₁₂ p₀₂ i` structure for a Kan complex, one may obtain
a `MulStruct p₀₁ p₁₂ p₀₂' i` structure when `p₀₂` and `p₀₂'` are homotopic. -/
@[no_expose]
noncomputable def MulStruct.unique'
    [KanComplex X] {p₀₁ p₁₂ p₀₂ p₀₂' : X.PtSimplex (n + 1) x} {i : Fin (n + 1)}
    (h : MulStruct p₀₁ p₁₂ p₀₂ i) (h₀₂ : RelStruct₀ p₀₂ p₀₂') :
    MulStruct p₀₁ p₁₂ p₀₂' i :=
  MulStruct.assoc' h (mulOne p₁₂ i)
    (relStructSuccEquivMulStruct (h₀₂.symm.relStruct i.succ))

end SSet.PtSimplex
