/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.BisimplicialRows
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
public import Mathlib.AlgebraicTopology.SimplicialSet.Monoidal
import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplices
import Mathlib.CategoryTheory.Limits.Types.Pushouts

/-!
# Skeletal filtration of a bisimplicial diagonal

This file constructs the horizontal latching subcomplexes of a bisimplicial
set, their finite degeneracy filtration, and the filtration of the diagonal by
the cells `X_n ⊗ Δ[n]`.  Consecutive stages are identified as explicit
pushouts.  The successor attachment has domain

`(L_(n+1) X ⊗ Δ[n+1]) ∪ (X_(n+1) ⊗ ∂Δ[n+1])`.

All constructions are natural in maps of bisimplicial sets.  This is purely
combinatorial: no properness, realization, weak-equivalence, or diagonal
homotopy-invariance statement is made.

The filtration and its two pushout families follow Goerss--Jardine,
*Simplicial Homotopy Theory*, IV, Proposition 1.9, equivalently Jardine,
Lecture 08, Lemma 21.1.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor Limits MonoidalCategory Opposite

open scoped Simplicial

universe u

namespace SSet

/-! ## A private pointwise pushout adapter -/

/-- A preimage square is also a pushout onto `B ⊔ range f` when `f` is
injective away from the preimage.  This implementation-only adapter is proved
pointwise in `Type`. -/
private theorem preimageSupRange_isPushout
    {K L : SSet.{u}} (B : L.Subcomplex) (f : K ⟶ L)
    (hinj : ∀ (a : SimplexCategoryᵒᵖ) (x y : K.obj a),
      x ∉ (B.preimage f).obj a → y ∉ (B.preimage f).obj a →
      f.app a x = f.app a y → x = y) :
    IsPushout (B.fromPreimage f) (B.preimage f).ι
      (Subcomplex.homOfLE
        (show B ≤ B ⊔ Subcomplex.range f from le_sup_left))
      (Subcomplex.lift f
        (show Subcomplex.range f ≤ B ⊔ Subcomplex.range f from le_sup_right)) := by
  have hw : B.fromPreimage f ≫
        Subcomplex.homOfLE
          (show B ≤ B ⊔ Subcomplex.range f from le_sup_left) =
      (B.preimage f).ι ≫
        Subcomplex.lift f
          (show Subcomplex.range f ≤ B ⊔ Subcomplex.range f from le_sup_right) := by
    apply (cancel_mono (B ⊔ Subcomplex.range f : L.Subcomplex).ι).mp
    simp only [Category.assoc, Subcomplex.homOfLE_ι, Subcomplex.lift_ι,
      Subcomplex.fromPreimage_ι]
  refine
    { w := hw
      isColimit' := ⟨evaluationJointlyReflectsColimits _ (fun a => ?_)⟩ }
  apply (isColimitMapCoconePushoutCoconeEquiv (SSet.evaluation.obj a) _).2
  apply IsPushout.isColimit
  let t : (B.preimage f : SSet.{u}).obj a ⟶ (B : SSet.{u}).obj a :=
    (B.fromPreimage f).app a
  let l : (B.preimage f : SSet.{u}).obj a ⟶ K.obj a :=
    (B.preimage f).ι.app a
  let r : (B : SSet.{u}).obj a ⟶
      ((B ⊔ Subcomplex.range f : L.Subcomplex) : SSet.{u}).obj a :=
    (Subcomplex.homOfLE
      (show B ≤ B ⊔ Subcomplex.range f from le_sup_left)).app a
  let b : K.obj a ⟶
      ((B ⊔ Subcomplex.range f : L.Subcomplex) : SSet.{u}).obj a :=
    (Subcomplex.lift f
      (show Subcomplex.range f ≤ B ⊔ Subcomplex.range f from le_sup_right)).app a
  change IsPushout t l r b
  have hmono : Mono r := by
    dsimp only [r]
    rw [mono_iff_injective]
    intro x y h
    exact Subtype.ext (congrArg (fun z => z.val) h)
  have hpull : IsPullback t l r b := by
    dsimp only [t, l, r, b]
    rw [CategoryTheory.Limits.Types.isPullback_iff]
    refine ⟨congr_app hw a, ?_, ?_⟩
    · intro x y h
      apply Subtype.ext
      exact h.2
    · intro x y h
      have hv := congrArg
        (fun z : ((B ⊔ Subcomplex.range f : L.Subcomplex) : SSet.{u}).obj a =>
          z.val) h
      have hxy : f.app a y = x.val := hv.symm
      have hy : y ∈ (B.preimage f).obj a := by
        change f.app a y ∈ B.obj a
        rw [hxy]
        exact x.2
      exact ⟨⟨y, hy⟩, Subtype.ext hxy, rfl⟩
  have hcover : Set.range r ⊔ Set.range b = Set.univ := by
    ext z
    constructor
    · intro
      trivial
    · intro
      rcases z with ⟨z, hz⟩
      have hzSup := hz
      change z ∈ B.obj a ∨ z ∈ Set.range (f.app a) at hz
      change (⟨z, hzSup⟩ :
        ((B ⊔ Subcomplex.range f : L.Subcomplex) : SSet.{u}).obj a) ∈
          Set.range r ∨
        (⟨z, hzSup⟩ :
          ((B ⊔ Subcomplex.range f : L.Subcomplex) : SSet.{u}).obj a) ∈
            Set.range b
      rcases hz with hz | ⟨x, rfl⟩
      · exact Or.inl ⟨⟨z, hz⟩, Subtype.ext rfl⟩
      · exact Or.inr ⟨x, Subtype.ext rfl⟩
  refine @CategoryTheory.Limits.Types.isPushout_of_isPullback_of_mono'
    _ _ _ _ _ _ _ _ hpull hmono hcover ?_
  intro x y hx hy hxy
  apply hinj a x y
  · intro hxmem
    exact hx ⟨⟨x, hxmem⟩, rfl⟩
  · intro hymem
    exact hy ⟨⟨y, hymem⟩, rfl⟩
  · exact congrArg (fun z => z.val) hxy

/-- A map that is degreewise injective off the preimage of a subcomplex
attaches its source to that subcomplex by an actual simplicial pushout. -/
theorem Subcomplex.preimageSupRange_isPushout
    {K L : SSet.{u}} (B : L.Subcomplex) (f : K ⟶ L)
    (hinj : ∀ (a : SimplexCategoryᵒᵖ) (x y : K.obj a),
      x ∉ (B.preimage f).obj a → y ∉ (B.preimage f).obj a →
      f.app a x = f.app a y → x = y) :
    IsPushout (B.fromPreimage f) (B.preimage f).ι
      (Subcomplex.homOfLE
        (show B ≤ B ⊔ Subcomplex.range f from le_sup_left))
      (Subcomplex.lift f
        (show Subcomplex.range f ≤ B ⊔ Subcomplex.range f from le_sup_right)) :=
  SSet.preimageSupRange_isPushout B f hinj

/-! ## Horizontal latching subcomplexes -/

/-- The outer latching subcomplex in degree `n`: at inner degree `a`, it is
the set of degenerate `n`-simplices of the outer row `simplicialRow X a`. -/
def outerLatching (X : SimplicialObject SSet.{u}) (n : ℕ) :
    (X.obj (op ⦋n⦌)).Subcomplex where
  obj a := (simplicialRow X a).degenerate n
  map {a b} k x hx := by
    exact degenerate_app_apply hx ((simplicialTransposeFunctor.obj X).map k)

@[simp]
theorem outerLatching_obj (X : SimplicialObject SSet.{u}) (n : ℕ)
    (a : SimplexCategoryᵒᵖ) :
    (outerLatching X n).obj a = (simplicialRow X a).degenerate n :=
  rfl

@[simp]
theorem outerLatching_zero (X : SimplicialObject SSet.{u}) :
    outerLatching X 0 = ⊥ := by
  ext a x
  change x ∈ (simplicialRow X a).degenerate 0 ↔ x ∈ (∅ : Set _)
  rw [SSet.degenerate_zero]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Membership in the outer latching object is exactly factorization through
a strictly smaller outer degree by an epimorphism in the simplex category. -/
theorem mem_outerLatching_iff (X : SimplicialObject SSet.{u}) (n : ℕ)
    (a : SimplexCategoryᵒᵖ) (x : (X.obj (op ⦋n⦌)).obj a) :
    x ∈ (outerLatching X n).obj a ↔
      ∃ (m : ℕ) (_ : m < n) (q : ⦋n⦌ ⟶ ⦋m⦌) (_ : Epi q)
        (y : (X.obj (op ⦋m⦌)).obj a),
        x = (X.map q.op).app a y := by
  change x ∈ (simplicialRow X a).degenerate n ↔ _
  rw [SSet.mem_degenerate_iff]
  simp only [Set.mem_range, simplicialRow_obj, simplicialRow_map]
  constructor
  · rintro ⟨m, hm, q, hq, y, hy⟩
    exact ⟨m, hm, q, hq, y, hy.symm⟩
  · rintro ⟨m, hm, q, hq, y, rfl⟩
    exact ⟨m, hm, q, hq, y, rfl⟩

/-- In successor degree, the outer latching subcomplex is the union of the
ranges of the outer degeneracies. -/
theorem outerLatching_succ_eq_iSup_range_sigma
    (X : SimplicialObject SSet.{u}) (n : ℕ) :
    outerLatching X (n + 1) =
      ⨆ (i : Fin (n + 1)), Subcomplex.range (X.σ i) := by
  ext a x
  change x ∈ (simplicialRow X a).degenerate (n + 1) ↔ _
  rw [SSet.degenerate_eq_iUnion_range_σ]
  change x ∈ ⋃ i, Set.range ((X.σ i).app a) ↔ _
  simp only [Subfunctor.iSup_obj, Set.mem_iUnion, Subcomplex.range,
    Subfunctor.range_obj]

/-- The finite union of the first outer-degeneracy images through index `r`. -/
def outerLatchingStage (X : SimplicialObject SSet.{u}) (n : ℕ)
    (r : Fin (n + 1)) : (X.obj (op ⦋n + 1⦌)).Subcomplex :=
  ⨆ (i : Fin (n + 1)), ⨆ (_ : i ≤ r), Subcomplex.range (X.σ i)

/-- Elementwise membership in a finite latching stage. -/
theorem mem_outerLatchingStage_iff
    (X : SimplicialObject SSet.{u}) (n : ℕ) (r : Fin (n + 1))
    (a : SimplexCategoryᵒᵖ) (x : (X.obj (op ⦋n + 1⦌)).obj a) :
    x ∈ (outerLatchingStage X n r).obj a ↔
      ∃ (i : Fin (n + 1)), i ≤ r ∧
        ∃ y : (X.obj (op ⦋n⦌)).obj a, (X.σ i).app a y = x := by
  simp only [outerLatchingStage, Subfunctor.iSup_obj, Set.mem_iUnion,
    Subcomplex.range, Subfunctor.range_obj, Set.mem_range]
  aesop

/-- The union of outer-degeneracy images strictly before index `r`. -/
def outerLatchingStageBefore (X : SimplicialObject SSet.{u}) (n : ℕ)
    (r : Fin (n + 1)) : (X.obj (op ⦋n + 1⦌)).Subcomplex :=
  ⨆ (i : Fin (n + 1)), ⨆ (_ : i < r), Subcomplex.range (X.σ i)

/-- The overlap between the already attached degeneracies and the image of
the degeneracy at `r`. -/
def outerLatchingStageOverlap (X : SimplicialObject SSet.{u}) (n : ℕ)
    (r : Fin (n + 1)) : (X.obj (op ⦋n + 1⦌)).Subcomplex :=
  outerLatchingStageBefore X n r ⊓ Subcomplex.range (X.σ r)

/-- Projection of the overlap to the already attached degeneracy union. -/
def outerLatchingOverlapToBefore
    (X : SimplicialObject SSet.{u}) (n : ℕ) (r : Fin (n + 1)) :
    (outerLatchingStageOverlap X n r : SSet.{u}) ⟶
      outerLatchingStageBefore X n r :=
  Subcomplex.homOfLE (by
    unfold outerLatchingStageOverlap
    exact inf_le_left)

/-- Projection of the overlap to the newly attached degeneracy range. -/
def outerLatchingOverlapToRange
    (X : SimplicialObject SSet.{u}) (n : ℕ) (r : Fin (n + 1)) :
    (outerLatchingStageOverlap X n r : SSet.{u}) ⟶
      Subcomplex.range (X.σ r) :=
  Subcomplex.homOfLE (by
    unfold outerLatchingStageOverlap
    exact inf_le_right)

@[reassoc (attr := simp)]
theorem outerLatchingOverlapToBefore_ι
    (X : SimplicialObject SSet.{u}) (n : ℕ) (r : Fin (n + 1)) :
    outerLatchingOverlapToBefore X n r ≫
        (outerLatchingStageBefore X n r).ι =
      (outerLatchingStageOverlap X n r).ι :=
  rfl

@[reassoc (attr := simp)]
theorem outerLatchingOverlapToRange_ι
    (X : SimplicialObject SSet.{u}) (n : ℕ) (r : Fin (n + 1)) :
    outerLatchingOverlapToRange X n r ≫
        (Subcomplex.range (X.σ r)).ι =
      (outerLatchingStageOverlap X n r).ι :=
  rfl

theorem outerLatchingStage_eq_before_sup_range
    (X : SimplicialObject SSet.{u}) (n : ℕ) (r : Fin (n + 1)) :
    outerLatchingStage X n r = outerLatchingStageBefore X n r ⊔
      Subcomplex.range (X.σ r) := by
  apply le_antisymm
  · unfold outerLatchingStage
    rw [iSup_le_iff]
    intro i
    rw [iSup_le_iff]
    intro hi
    rcases hi.lt_or_eq with hi | rfl
    · exact le_sup_of_le_left (le_iSup_of_le i (le_iSup_of_le hi (by rfl)))
    · exact le_sup_right
  · apply sup_le
    · unfold outerLatchingStageBefore outerLatchingStage
      rw [iSup_le_iff]
      intro i
      rw [iSup_le_iff]
      intro hi
      exact le_iSup_of_le i (le_iSup_of_le hi.le (by rfl))
    · exact le_iSup_of_le r (le_iSup_of_le (le_refl r) (by rfl))

@[simp]
theorem outerLatchingStage_zero (X : SimplicialObject SSet.{u}) (n : ℕ) :
    outerLatchingStage X n 0 =
      Subcomplex.range (X.σ (0 : Fin (n + 1))) := by
  rw [outerLatchingStage_eq_before_sup_range]
  have hbot : outerLatchingStageBefore X n 0 = ⊥ := by
    apply le_antisymm
    · unfold outerLatchingStageBefore
      rw [iSup_le_iff]
      intro i
      rw [iSup_le_iff]
      intro hi
      exact (Fin.not_lt_zero i hi).elim
    · exact bot_le
  rw [hbot, bot_sup_eq]

/-- The first finite latching stage is the image of `σ₀`, hence canonically
isomorphic to the preceding outer degree. -/
noncomputable def outerLatchingStage_zero_iso
    (X : SimplicialObject SSet.{u}) (n : ℕ) :
    X.obj (op ⦋n⦌) ≅ (outerLatchingStage X n 0 : SSet.{u}) := by
  haveI : Mono (X.σ (0 : Fin (n + 1))) :=
    SimplicialObject.mono_sigma X (0 : Fin (n + 1))
  exact asIso (Subcomplex.toRange (X.σ (0 : Fin (n + 1)))) ≪≫
    Subcomplex.eqToIso (outerLatchingStage_zero X n).symm

@[reassoc]
theorem outerLatchingStage_zero_iso_hom_ι
    (X : SimplicialObject SSet.{u}) (n : ℕ) :
    (outerLatchingStage_zero_iso X n).hom ≫
        (outerLatchingStage X n 0).ι = X.σ (0 : Fin (n + 1)) := by
  simp [outerLatchingStage_zero_iso]

/-- The last finite latching stage is the whole latching subcomplex. -/
theorem outerLatchingStage_last
    (X : SimplicialObject SSet.{u}) (n : ℕ) :
    outerLatchingStage X n (Fin.last n) = outerLatching X (n + 1) := by
  rw [outerLatching_succ_eq_iSup_range_sigma]
  apply le_antisymm
  · unfold outerLatchingStage
    rw [iSup_le_iff]
    intro i
    rw [iSup_le_iff]
    intro _
    exact le_iSup
      (fun j : Fin (n + 1) => Subcomplex.range (X.σ j)) i
  · rw [iSup_le_iff]
    intro i
    exact le_iSup_of_le i (le_iSup_of_le (Fin.le_last i) (by rfl))

/-- Elementwise description of the overlap.  The first witness uses an index
strictly before `r`, and the second uses exactly `r`. -/
theorem mem_outerLatchingStageOverlap_iff
    (X : SimplicialObject SSet.{u}) (n : ℕ) (r : Fin (n + 1))
    (a : SimplexCategoryᵒᵖ) (x : (X.obj (op ⦋n + 1⦌)).obj a) :
    x ∈ (outerLatchingStageOverlap X n r).obj a ↔
      (∃ (i : Fin (n + 1)), i < r ∧
        ∃ y : (X.obj (op ⦋n⦌)).obj a, (X.σ i).app a y = x) ∧
      ∃ y : (X.obj (op ⦋n⦌)).obj a, (X.σ r).app a y = x := by
  simp only [outerLatchingStageOverlap, outerLatchingStageBefore,
    Subfunctor.min_obj, Set.mem_inter_iff, Subfunctor.iSup_obj,
    Set.mem_iUnion, Subcomplex.range, Subfunctor.range_obj, Set.mem_range]
  aesop

/-- The overlap pulled back to the source of the newly attached degeneracy. -/
abbrev outerLatchingStageSourceOverlap
    (X : SimplicialObject SSet.{u}) (n : ℕ) (r : Fin (n + 1)) :
    (X.obj (op ⦋n⦌)).Subcomplex :=
  (outerLatchingStageBefore X n r).preimage (X.σ r)

/-- A source simplex belongs to the overlap exactly when its `r`-th
degeneracy also has a presentation through an earlier degeneracy. -/
theorem mem_outerLatchingStageSourceOverlap_iff
    (X : SimplicialObject SSet.{u}) (n : ℕ) (r : Fin (n + 1))
    (a : SimplexCategoryᵒᵖ) (x : (X.obj (op ⦋n⦌)).obj a) :
    x ∈ (outerLatchingStageSourceOverlap X n r).obj a ↔
      ∃ (i : Fin (n + 1)), i < r ∧
        ∃ y : (X.obj (op ⦋n⦌)).obj a,
          (X.σ i).app a y = (X.σ r).app a x := by
  simp only [outerLatchingStageSourceOverlap, Subcomplex.preimage_obj,
    Set.mem_preimage, outerLatchingStageBefore, Subfunctor.iSup_obj,
    Set.mem_iUnion, Subcomplex.range, Subfunctor.range_obj, Set.mem_range]
  aesop

@[simp]
theorem outerLatchingStageSourceOverlap_zero
    (X : SimplicialObject SSet.{u}) (n : ℕ) :
    outerLatchingStageSourceOverlap X n 0 = ⊥ := by
  ext a x
  rw [mem_outerLatchingStageSourceOverlap_iff]
  simp

/-- At a successor degeneracy index, the source overlap is exactly the
preceding finite latching stage one outer degree lower. -/
theorem outerLatchingStageSourceOverlap_succ
    (X : SimplicialObject SSet.{u}) (n : ℕ) (r : Fin (n + 1)) :
    outerLatchingStageSourceOverlap X (n + 1) r.succ =
      outerLatchingStage X n r := by
  ext a x
  rw [mem_outerLatchingStageSourceOverlap_iff,
    mem_outerLatchingStage_iff]
  constructor
  · rintro ⟨i, hi, y, hxy⟩
    have hir : i ≤ r.castSucc := by
      apply Fin.le_iff_val_le_val.mpr
      exact Nat.le_of_lt_succ hi
    rcases hir.lt_or_eq with hlt | heq
    · let j : Fin (n + 1) :=
        ⟨i.val, lt_of_le_of_lt (Fin.le_iff_val_le_val.mp hir) r.isLt⟩
      have hij : j.castSucc = i := Fin.ext rfl
      have hjr : j ≤ r := by
        apply Fin.le_iff_val_le_val.mpr
        exact Nat.le_of_lt (by simpa [j, Fin.lt_def] using hlt)
      have hlt' : j.castSucc < r.castSucc := by simpa [hij] using hlt
      have hcomp : X.σ i ≫ X.δ r.succ.castSucc =
          X.δ r.castSucc ≫ X.σ j := by
        rw [← hij]
        simpa only [Fin.succ_castSucc] using
          X.δ_comp_σ_of_gt (i := r.castSucc) (j := j) hlt'
      have hret : X.σ r.succ ≫ X.δ r.succ.castSucc = 𝟙 _ :=
        X.δ_comp_σ_self
      have happ := congrArg
        (fun z => (X.δ r.succ.castSucc).app a z) hxy
      have hout :
          (X.σ j).app a ((X.δ r.castSucc).app a y) = x := by
        exact (ConcreteCategory.congr_hom (congr_app hcomp a) y).symm |>.trans
          (happ.trans (ConcreteCategory.congr_hom (congr_app hret a) x))
      exact ⟨j, hjr, (X.δ r.castSucc).app a y, hout⟩
    · subst i
      have hleft₁ : X.σ r.castSucc ≫ X.δ r.succ.castSucc = 𝟙 _ := by
        simpa only [Fin.succ_castSucc] using
          (X.δ_comp_σ_succ (i := r.castSucc))
      have hright₁ : X.σ r.succ ≫ X.δ r.succ.castSucc = 𝟙 _ :=
        X.δ_comp_σ_self
      have happ₁ := congrArg
        (fun z => (X.δ r.succ.castSucc).app a z) hxy
      have hyx : y = x := by
        exact (ConcreteCategory.congr_hom (congr_app hleft₁ a) y).symm |>.trans
          (happ₁.trans
            (ConcreteCategory.congr_hom (congr_app hright₁ a) x))
      have hleft₂ : X.σ r.castSucc ≫ X.δ r.castSucc.castSucc = 𝟙 _ :=
        X.δ_comp_σ_self
      have hright₂ : X.σ r.succ ≫ X.δ r.castSucc.castSucc =
          X.δ r.castSucc ≫ X.σ r :=
        X.δ_comp_σ_of_le (i := r.castSucc) (j := r) (by rfl)
      have happ₂ := congrArg
        (fun z => (X.δ r.castSucc.castSucc).app a z) hxy
      have hydeg : y =
          (X.σ r).app a ((X.δ r.castSucc).app a x) := by
        exact (ConcreteCategory.congr_hom (congr_app hleft₂ a) y).symm |>.trans
          (happ₂.trans
            (ConcreteCategory.congr_hom (congr_app hright₂ a) x))
      exact ⟨r, le_refl r, (X.δ r.castSucc).app a x,
        hydeg.symm.trans hyx⟩
  · rintro ⟨j, hjr, y, rfl⟩
    refine ⟨j.castSucc, ?_, (X.σ r).app a y, ?_⟩
    · simpa only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] using
        Nat.lt_succ_of_le (Fin.le_iff_val_le_val.mp hjr)
    · exact ConcreteCategory.congr_hom
        (congr_app (X.σ_comp_σ hjr) a) y

/-- The newly attached degeneracy with codomain restricted to its finite
latching stage. -/
noncomputable def outerDegeneracyToLatchingStage
    (X : SimplicialObject SSet.{u}) (n : ℕ) (r : Fin (n + 1)) :
    X.obj (op ⦋n⦌) ⟶ (outerLatchingStage X n r : SSet.{u}) :=
  Subcomplex.lift (X.σ r) (by exact le_sup_right) ≫
    (Subcomplex.eqToIso
      (outerLatchingStage_eq_before_sup_range X n r).symm).hom

@[reassoc]
theorem outerDegeneracyToLatchingStage_ι
    (X : SimplicialObject SSet.{u}) (n : ℕ) (r : Fin (n + 1)) :
    outerDegeneracyToLatchingStage X n r ≫
        (outerLatchingStage X n r).ι = X.σ r := by
  simp [outerDegeneracyToLatchingStage]

/-- The standard degeneracy-overlap square, with the lower-left object the
actual preceding outer degree, is a pushout.  Injectivity of its new-cell map
uses the simplicial retraction `σ r ≫ δ r.castSucc = id`. -/
theorem outerLatchingStageSource_isPushout
    (X : SimplicialObject SSet.{u}) (n : ℕ) (r : Fin (n + 1)) :
    IsPushout
      ((outerLatchingStageBefore X n r).fromPreimage (X.σ r))
      (outerLatchingStageSourceOverlap X n r).ι
      (Subcomplex.homOfLE (by
        rw [outerLatchingStage_eq_before_sup_range]
        exact le_sup_left))
      (outerDegeneracyToLatchingStage X n r) := by
  let h := preimageSupRange_isPushout
    (outerLatchingStageBefore X n r) (X.σ r) (by
      intro a x y _ _ hxy
      have h' := congrArg (fun z => (X.δ r.castSucc).app a z) hxy
      simpa [← comp_apply, ← NatTrans.comp_app,
        X.δ_comp_σ_self] using h')
  exact h.of_iso (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (Subcomplex.eqToIso
      (outerLatchingStage_eq_before_sup_range X n r).symm)
    (by rfl) (by rfl)
    (by
      apply (cancel_mono (outerLatchingStage X n r).ι).mp
      simp)
    (by
      apply (cancel_mono (outerLatchingStage X n r).ι).mp
      simp [outerDegeneracyToLatchingStage])

/-! ## Diagonal cells and their filtration -/

/-- The degree-`n` cell map into the diagonal of a bisimplicial set.  A pair
`(x, θ : [m] ⟶ [n])` is sent to the outer reindexing of `x` along `θ`. -/
noncomputable def diagonalCellMap (X : SimplicialObject SSet.{u}) (n : ℕ) :
    X.obj (op ⦋n⦌) ⊗ Δ[n] ⟶ simplicialDiagonalFunctor.obj X where
  app a := ↾fun z =>
    (X.map (stdSimplex.objEquiv z.2).op).app a z.1
  naturality {a b} k := by
    apply ConcreteCategory.hom_ext
    rintro ⟨x, θ⟩
    change
      (X.map (stdSimplex.objEquiv ((Δ[n] : SSet.{u}).map k θ)).op).app b
          ((X.obj (op ⦋n⦌)).map k x) =
        (X.map k).app b ((X.obj a).map k
          ((X.map (stdSimplex.objEquiv θ).op).app a x))
    rw [stdSimplex.map_apply]
    change
      (X.map ((k.unop ≫ stdSimplex.objEquiv θ).op)).app b
          ((X.obj (op ⦋n⦌)).map k x) = _
    rw [op_comp, Functor.map_comp, NatTrans.comp_app, comp_apply]
    rw [NatTrans.naturality_apply]
    rfl

@[simp]
theorem diagonalCellMap_app_apply
    (X : SimplicialObject SSet.{u}) (n : ℕ)
    (a : SimplexCategoryᵒᵖ) (x : (X.obj (op ⦋n⦌)).obj a)
    (θ : (Δ[n] : SSet.{u}).obj a) :
    (diagonalCellMap X n).app a ⟨x, θ⟩ =
      (X.map (stdSimplex.objEquiv θ).op).app a x :=
  rfl

@[simp]
theorem diagonalCellMap_identity
    (X : SimplicialObject SSet.{u}) (n : ℕ)
    (x : (X.obj (op ⦋n⦌)).obj (op ⦋n⦌)) :
    (diagonalCellMap X n).app (op ⦋n⦌)
        ⟨x, stdSimplex.objEquiv.symm (𝟙 ⦋n⦌)⟩ = x := by
  change (X.map (𝟙 (op ⦋n⦌))).app (op ⦋n⦌) x = x
  rw [X.map_id]
  rfl

/-- The first `n` horizontal cell degrees inside the diagonal. -/
noncomputable def diagonalFiltration (X : SimplicialObject SSet.{u}) (n : ℕ) :
    (simplicialDiagonalFunctor.obj X).Subcomplex :=
  ⨆ (p : ℕ), ⨆ (_ : p ≤ n), Subcomplex.range (diagonalCellMap X p)

/-- Membership in the diagonal filtration is an explicit bounded outer-degree
factorization. -/
theorem mem_diagonalFiltration_iff
    (X : SimplicialObject SSet.{u}) (n m : ℕ)
    (z : (simplicialDiagonalFunctor.obj X).obj (op ⦋m⦌)) :
    z ∈ (diagonalFiltration X n).obj (op ⦋m⦌) ↔
      ∃ (p : ℕ) (_ : p ≤ n)
        (x : (X.obj (op ⦋p⦌)).obj (op ⦋m⦌)) (θ : ⦋m⦌ ⟶ ⦋p⦌),
        z = (X.map θ.op).app (op ⦋m⦌) x := by
  simp only [diagonalFiltration, Subfunctor.iSup_obj, Set.mem_iUnion,
    Subcomplex.range, Subfunctor.range_obj, Set.mem_range]
  constructor
  · rintro ⟨p, hp, ⟨x, θ⟩, hz⟩
    exact ⟨p, hp, x, stdSimplex.objEquiv θ, hz.symm⟩
  · rintro ⟨p, hp, x, θ, rfl⟩
    exact ⟨p, hp, ⟨x, stdSimplex.objEquiv.symm θ⟩, rfl⟩

theorem diagonalFiltration_monotone (X : SimplicialObject SSet.{u}) :
    Monotone (diagonalFiltration X) := by
  intro n m h
  unfold diagonalFiltration
  rw [iSup_le_iff]
  intro p
  rw [iSup_le_iff]
  intro hp
  exact le_iSup_of_le p (le_iSup_of_le (hp.trans h) (by rfl))

/-- Inclusion between two bounded diagonal-filtration stages. -/
noncomputable def diagonalFiltrationMap (X : SimplicialObject SSet.{u}) {n m : ℕ}
    (h : n ≤ m) :
    (diagonalFiltration X n : SSet.{u}) ⟶ diagonalFiltration X m :=
  Subcomplex.homOfLE (diagonalFiltration_monotone X h)

instance diagonalFiltrationMap_mono (X : SimplicialObject SSet.{u})
    {n m : ℕ} (h : n ≤ m) : Mono (diagonalFiltrationMap X h) :=
  by dsimp [diagonalFiltrationMap]; infer_instance

theorem diagonalFiltration_succ
    (X : SimplicialObject SSet.{u}) (n : ℕ) :
    diagonalFiltration X (n + 1) = diagonalFiltration X n ⊔
      Subcomplex.range (diagonalCellMap X (n + 1)) := by
  apply le_antisymm
  · unfold diagonalFiltration
    rw [iSup_le_iff]
    intro p
    rw [iSup_le_iff]
    intro hp
    rcases hp.lt_or_eq with hp | hp
    · exact le_sup_of_le_left
        (le_iSup_of_le p (le_iSup_of_le (Nat.le_of_lt_succ hp) (by rfl)))
    · obtain rfl : p = n + 1 := by omega
      exact le_sup_right
  · apply sup_le
    · exact diagonalFiltration_monotone X (Nat.le_succ n)
    · exact le_iSup_of_le (n + 1)
        (le_iSup_of_le (le_refl (n + 1)) (by rfl))

theorem diagonalFiltration_zero
    (X : SimplicialObject SSet.{u}) :
    diagonalFiltration X 0 = Subcomplex.range (diagonalCellMap X 0) := by
  apply le_antisymm
  · unfold diagonalFiltration
    rw [iSup_le_iff]
    intro p
    rw [iSup_le_iff]
    intro hp
    obtain rfl : p = 0 := Nat.eq_zero_of_le_zero hp
    rfl
  · exact le_iSup_of_le 0 (le_iSup_of_le (le_refl 0) (by rfl))

theorem diagonalCellMap_zero_mono
    (X : SimplicialObject SSet.{u}) : Mono (diagonalCellMap X 0) := by
  rw [NatTrans.mono_iff_mono_app]
  intro a
  rw [mono_iff_injective]
  rintro ⟨x, θ⟩ ⟨y, φ⟩ h
  have hθ : θ = φ :=
    stdSimplex.objEquiv.injective (Subsingleton.elim _ _)
  subst φ
  apply Prod.ext
  · let q := stdSimplex.objEquiv θ
    have : Epi q := by
      rw [SimplexCategory.epi_iff_surjective]
      intro j
      exact ⟨0, (Fin.eq_zero _).trans (Fin.eq_zero j).symm⟩
    obtain ⟨⟨hq⟩⟩ := isSplitEpi_of_epi q
    change (X.map q.op).app a x = (X.map q.op).app a y at h
    have h' := congrArg
      (fun z => (X.map hq.section_.op).app a z) h
    simpa [diagonalCellMap, q, ← comp_apply, ← NatTrans.comp_app,
      ← Functor.map_comp, ← op_comp] using h'
  · rfl

/-- The zeroth diagonal filtration stage is the range of its zeroth cell. -/
noncomputable def diagonalFiltration_zero_iso
    (X : SimplicialObject SSet.{u}) :
    X.obj (op ⦋0⦌) ⊗ Δ[0] ≅ (diagonalFiltration X 0 : SSet.{u}) := by
  have : Mono (diagonalCellMap X 0) := diagonalCellMap_zero_mono X
  exact asIso (Subcomplex.toRange (diagonalCellMap X 0)) ≪≫
    Subcomplex.eqToIso (diagonalFiltration_zero X).symm

/-- Every diagonal simplex occurs in the cell having its own degree and the
identity standard simplex. -/
theorem iSup_diagonalFiltration_eq_top
    (X : SimplicialObject SSet.{u}) :
    ⨆ (n : ℕ), diagonalFiltration X n = ⊤ := by
  apply top_unique
  intro a z hz
  induction a using Opposite.rec with
  | _ a =>
    induction a using SimplexCategory.rec with
    | _ m =>
      simp only [Subfunctor.iSup_obj, Set.mem_iUnion]
      refine ⟨m, (mem_diagonalFiltration_iff X m m z).2 ?_⟩
      refine ⟨m, le_refl m, z, 𝟙 _, ?_⟩
      rw [op_id, X.map_id]
      rfl

/-! ## Successor attachments -/

/-- The union-product boundary of the degree-`n+1` diagonal cell. -/
def diagonalAttachmentDomain (X : SimplicialObject SSet.{u}) (n : ℕ) :
    (X.obj (op ⦋n + 1⦌) ⊗ Δ[n + 1]).Subcomplex :=
  (outerLatching X (n + 1)).unionProd (boundary (n + 1))

set_option backward.isDefEq.respectTransparency false in
private theorem diagonalCellMap_nonDegenerate_not_mem
    (X : SimplicialObject SSet.{u}) (n m : ℕ)
    (x : (X.obj (op ⦋n + 1⦌)).obj (op ⦋m⦌))
    (hx : x ∈ (simplicialRow X (op ⦋m⦌)).nonDegenerate (n + 1))
    (θ : ⦋m⦌ ⟶ ⦋n + 1⦌) [Epi θ] :
    (X.map θ.op).app (op ⦋m⦌) x ∉
      (diagonalFiltration X n).obj (op ⦋m⦌) := by
  intro hz
  obtain ⟨p, hp, y, φ, hφ⟩ :=
    (mem_diagonalFiltration_iff X n m _).1 hz
  let R := simplicialRow X (op ⦋m⦌)
  let z : R _⦋m⦌ := (X.map θ.op).app (op ⦋m⦌) x
  let sz : R.S := S.mk z
  let yR : R _⦋p⦌ := by
    change (X.obj (op ⦋p⦌)).obj (op ⦋m⦌)
    exact y
  let sy : R.S := S.mk yR
  have hθrep : z = R.map θ.op x := rfl
  have hφrep : z = R.map φ.op yR := hφ.trans rfl
  have hdim : n + 1 = sz.toN.dim := by
    exact R.unique_nonDegenerate_dim z θ ⟨x, hx⟩ hθrep sz.toNπ
      ⟨sz.toN.simplex, sz.toN.nonDegenerate⟩
      (S.map_toNπ_op_apply sz).symm
  have hle : sz ≤ sy := by
    change S.mk z ≤ S.mk yR
    rw [hφrep]
    exact S.mk_map_le yR φ
  have hleN : sz.toN ≤ sy.toN := by
    rw [N.le_iff, S.subcomplex_toN, S.subcomplex_toN]
    exact hle
  have hdimle : sz.toN.dim ≤ p :=
    (N.dim_le_of_le hleN).trans (S.dim_toN_le sy)
  omega

set_option backward.isDefEq.respectTransparency false in
/-- The boundary union-product is exactly the preimage of the preceding
diagonal-filtration stage under the new cell map. -/
theorem diagonalAttachmentDomain_eq_preimage
    (X : SimplicialObject SSet.{u}) (n : ℕ) :
    diagonalAttachmentDomain X n =
      (diagonalFiltration X n).preimage (diagonalCellMap X (n + 1)) := by
  unfold diagonalAttachmentDomain
  ext a z
  induction a using Opposite.rec with
  | _ a =>
    induction a using SimplexCategory.rec with
    | _ m =>
      rcases z with ⟨x, s⟩
      let θ : ⦋m⦌ ⟶ ⦋n + 1⦌ := stdSimplex.objEquiv s
      change
        ⟨x, s⟩ ∈ ((outerLatching X (n + 1)).unionProd
            (boundary (n + 1))).obj (op ⦋m⦌) ↔
          (diagonalCellMap X (n + 1)).app (op ⦋m⦌) ⟨x, s⟩ ∈
            (diagonalFiltration X n).obj (op ⦋m⦌)
      rw [Subcomplex.mem_unionProd_iff]
      change
        s ∈ (boundary (n + 1)).obj (op ⦋m⦌) ∨
            x ∈ (outerLatching X (n + 1)).obj (op ⦋m⦌) ↔
          (X.map θ.op).app (op ⦋m⦌) x ∈
            (diagonalFiltration X n).obj (op ⦋m⦌)
      constructor
      · rintro (hs | hx)
        · have hnot : ¬Function.Surjective θ.toOrderHom := hs
          obtain ⟨i, θ', hθ⟩ :=
            SimplexCategory.eq_comp_δ_of_not_surjective θ hnot
          apply (mem_diagonalFiltration_iff X n m _).2
          refine ⟨n, le_refl n,
            (X.map (SimplexCategory.δ i).op).app (op ⦋m⦌) x, θ', ?_⟩
          rw [hθ, op_comp, Functor.map_comp, NatTrans.comp_app, comp_apply]
        · obtain ⟨p, hp, q, hq, y, rfl⟩ :=
            (mem_outerLatching_iff X (n + 1) (op ⦋m⦌) x).1 hx
          apply (mem_diagonalFiltration_iff X n m _).2
          refine ⟨p, Nat.le_of_lt_succ hp, y, θ ≫ q, ?_⟩
          simp only [op_comp, Functor.map_comp, NatTrans.comp_app, comp_apply]
      · intro hz
        by_contra hmem
        push Not at hmem
        have hθEpi : Epi θ := by
          rw [SimplexCategory.epi_iff_surjective]
          by_contra hsurj
          exact hmem.1 hsurj
        have hxNon :
            x ∈ (simplicialRow X (op ⦋m⦌)).nonDegenerate (n + 1) := by
          rw [mem_nonDegenerate_iff_notMem_degenerate]
          exact hmem.2
        exact diagonalCellMap_nonDegenerate_not_mem X n m x hxNon θ hz

/-- The attaching map from the union-product boundary into the preceding
diagonal-filtration stage. -/
noncomputable def diagonalAttachmentTopMap
    (X : SimplicialObject SSet.{u}) (n : ℕ) :
    (diagonalAttachmentDomain X n : SSet.{u}) ⟶ diagonalFiltration X n :=
  (Subcomplex.eqToIso
      (diagonalAttachmentDomain_eq_preimage X n)).hom ≫
    (diagonalFiltration X n).fromPreimage (diagonalCellMap X (n + 1))

@[reassoc]
theorem diagonalAttachmentTopMap_ι
    (X : SimplicialObject SSet.{u}) (n : ℕ) :
    diagonalAttachmentTopMap X n ≫ (diagonalFiltration X n).ι =
      (diagonalAttachmentDomain X n).ι ≫
        diagonalCellMap X (n + 1) := by
  simp [diagonalAttachmentTopMap]

/-- The new cell, with codomain restricted to the successor filtration. -/
noncomputable def diagonalCellToFiltrationSucc
    (X : SimplicialObject SSet.{u}) (n : ℕ) :
    X.obj (op ⦋n + 1⦌) ⊗ Δ[n + 1] ⟶
      (diagonalFiltration X (n + 1) : SSet.{u}) :=
  Subcomplex.lift (diagonalCellMap X (n + 1)) (by exact le_sup_right) ≫
    (Subcomplex.eqToIso (diagonalFiltration_succ X n).symm).hom

@[reassoc]
theorem diagonalCellToFiltrationSucc_ι
    (X : SimplicialObject SSet.{u}) (n : ℕ) :
    diagonalCellToFiltrationSucc X n ≫
        (diagonalFiltration X (n + 1)).ι =
      diagonalCellMap X (n + 1) := by
  simp [diagonalCellToFiltrationSucc]

set_option backward.isDefEq.respectTransparency false in
private theorem diagonalCellMap_injective_off_attachment
    (X : SimplicialObject SSet.{u}) (n : ℕ)
    (a : SimplexCategoryᵒᵖ)
    (z₁ z₂ : (X.obj (op ⦋n + 1⦌) ⊗ Δ[n + 1]).obj a)
    (hz₁ : z₁ ∉ ((diagonalFiltration X n).preimage
      (diagonalCellMap X (n + 1))).obj a)
    (hz₂ : z₂ ∉ ((diagonalFiltration X n).preimage
      (diagonalCellMap X (n + 1))).obj a)
    (h : (diagonalCellMap X (n + 1)).app a z₁ =
      (diagonalCellMap X (n + 1)).app a z₂) :
    z₁ = z₂ := by
  induction a using Opposite.rec with
  | _ a =>
    induction a using SimplexCategory.rec with
    | _ m =>
      rcases z₁ with ⟨x₁, s₁⟩
      rcases z₂ with ⟨x₂, s₂⟩
      let θ₁ : ⦋m⦌ ⟶ ⦋n + 1⦌ := stdSimplex.objEquiv s₁
      let θ₂ : ⦋m⦌ ⟶ ⦋n + 1⦌ := stdSimplex.objEquiv s₂
      have hnot₁ :
          ¬(s₁ ∈ (boundary (n + 1)).obj (op ⦋m⦌) ∨
            x₁ ∈ (outerLatching X (n + 1)).obj (op ⦋m⦌)) := by
        rw [← diagonalAttachmentDomain_eq_preimage] at hz₁
        unfold diagonalAttachmentDomain at hz₁
        rw [Subcomplex.mem_unionProd_iff] at hz₁
        exact hz₁
      have hnot₂ :
          ¬(s₂ ∈ (boundary (n + 1)).obj (op ⦋m⦌) ∨
            x₂ ∈ (outerLatching X (n + 1)).obj (op ⦋m⦌)) := by
        rw [← diagonalAttachmentDomain_eq_preimage] at hz₂
        unfold diagonalAttachmentDomain at hz₂
        rw [Subcomplex.mem_unionProd_iff] at hz₂
        exact hz₂
      push Not at hnot₁ hnot₂
      have hθ₁ : Epi θ₁ := by
        rw [SimplexCategory.epi_iff_surjective]
        by_contra hsurj
        exact hnot₁.1 hsurj
      let R := simplicialRow X (op ⦋m⦌)
      let x₁R : R _⦋n + 1⦌ := by
        change (X.obj (op ⦋n + 1⦌)).obj (op ⦋m⦌)
        exact x₁
      let x₂R : R _⦋n + 1⦌ := by
        change (X.obj (op ⦋n + 1⦌)).obj (op ⦋m⦌)
        exact x₂
      have hx₁ : x₁R ∈ R.nonDegenerate (n + 1) := by
          rw [mem_nonDegenerate_iff_notMem_degenerate]
          exact hnot₁.2
      have hx₂ : x₂R ∈ R.nonDegenerate (n + 1) := by
        rw [mem_nonDegenerate_iff_notMem_degenerate]
        exact hnot₂.2
      have hR : R.map θ₁.op x₁R = R.map θ₂.op x₂R := h
      have hxEq : x₁ = x₂ := by
        exact congrArg Subtype.val
          (R.unique_nonDegenerate_simplex (R.map θ₁.op x₁R)
            θ₁ ⟨x₁R, hx₁⟩ rfl θ₂ ⟨x₂R, hx₂⟩ hR)
      have hθEq : θ₁ = θ₂ :=
        R.unique_nonDegenerate_map (R.map θ₁.op x₁R)
          θ₁ ⟨x₁R, hx₁⟩ rfl θ₂ ⟨x₂R, hx₂⟩ hR
      apply Prod.ext hxEq
      exact stdSimplex.objEquiv.injective hθEq

/-- The successor diagonal filtration is obtained by attaching the
degree-`n+1` cell along the stated union-product boundary. -/
theorem diagonalFiltrationSucc_isPushout
    (X : SimplicialObject SSet.{u}) (n : ℕ) :
    IsPushout (diagonalAttachmentTopMap X n)
      (diagonalAttachmentDomain X n).ι
      (diagonalFiltrationMap X (Nat.le_succ n))
      (diagonalCellToFiltrationSucc X n) := by
  let h := preimageSupRange_isPushout
    (diagonalFiltration X n) (diagonalCellMap X (n + 1))
    (diagonalCellMap_injective_off_attachment X n)
  exact h.of_iso
    (Subcomplex.eqToIso (diagonalAttachmentDomain_eq_preimage X n).symm)
    (Iso.refl _) (Iso.refl _)
    (Subcomplex.eqToIso (diagonalFiltration_succ X n).symm)
    (by
      apply (cancel_mono (diagonalFiltration X n).ι).mp
      simp [diagonalAttachmentTopMap])
    (by simp)
    (by
      apply (cancel_mono (diagonalFiltration X (n + 1)).ι).mp
      simp [diagonalFiltrationMap])
    (by simp [diagonalCellToFiltrationSucc])

/-! ## Functoriality -/

set_option backward.isDefEq.respectTransparency false in
/-- A map of bisimplicial sets restricts to every outer latching object. -/
def outerLatchingMap {X Y : SimplicialObject SSet.{u}} (η : X ⟶ Y)
    (n : ℕ) :
    (outerLatching X n : SSet.{u}) ⟶ outerLatching Y n :=
  Subcomplex.lift ((outerLatching X n).ι ≫ η.app (op ⦋n⦌)) (by
    rintro a _ ⟨⟨x, hx⟩, rfl⟩
    change (η.app (op ⦋n⦌)).app a x ∈
      (simplicialRow Y a).degenerate n
    exact degenerate_app_apply hx
      ((simplicialTransposeFunctor.map η).app a))

@[reassoc (attr := simp)]
theorem outerLatchingMap_ι {X Y : SimplicialObject SSet.{u}}
    (η : X ⟶ Y) (n : ℕ) :
    outerLatchingMap η n ≫ (outerLatching Y n).ι =
      (outerLatching X n).ι ≫ η.app (op ⦋n⦌) :=
  Subcomplex.lift_ι _ _

@[simp]
theorem outerLatchingMap_id (X : SimplicialObject SSet.{u}) (n : ℕ) :
    outerLatchingMap (𝟙 X) n = 𝟙 _ := by
  apply (cancel_mono (outerLatching X n).ι).mp
  simp

@[reassoc]
theorem outerLatchingMap_comp
    {X Y Z : SimplicialObject SSet.{u}} (η : X ⟶ Y) (θ : Y ⟶ Z)
    (n : ℕ) :
    outerLatchingMap (η ≫ θ) n =
      outerLatchingMap η n ≫ outerLatchingMap θ n := by
  apply (cancel_mono (outerLatching Z n).ι).mp
  simp

private theorem outerLatchingStage_map_mem
    {X Y : SimplicialObject SSet.{u}} (η : X ⟶ Y)
    (n : ℕ) (r : Fin (n + 1)) (a : SimplexCategoryᵒᵖ)
    (x : (X.obj (op ⦋n + 1⦌)).obj a)
    (hx : x ∈ (outerLatchingStage X n r).obj a) :
    (η.app (op ⦋n + 1⦌)).app a x ∈
      (outerLatchingStage Y n r).obj a := by
  simp only [outerLatchingStage, Subfunctor.iSup_obj, Set.mem_iUnion,
    Subcomplex.range, Subfunctor.range_obj, Set.mem_range] at hx ⊢
  obtain ⟨i, hi, y, rfl⟩ := hx
  refine ⟨i, hi, (η.app (op ⦋n⦌)).app a y, ?_⟩
  exact ConcreteCategory.congr_hom
    (congr_app (SimplicialObject.σ_naturality η i) a) y |>.symm

private theorem outerLatchingStageBefore_map_mem
    {X Y : SimplicialObject SSet.{u}} (η : X ⟶ Y)
    (n : ℕ) (r : Fin (n + 1)) (a : SimplexCategoryᵒᵖ)
    (x : (X.obj (op ⦋n + 1⦌)).obj a)
    (hx : x ∈ (outerLatchingStageBefore X n r).obj a) :
    (η.app (op ⦋n + 1⦌)).app a x ∈
      (outerLatchingStageBefore Y n r).obj a := by
  simp only [outerLatchingStageBefore, Subfunctor.iSup_obj, Set.mem_iUnion,
    Subcomplex.range, Subfunctor.range_obj, Set.mem_range] at hx ⊢
  obtain ⟨i, hi, y, rfl⟩ := hx
  refine ⟨i, hi, (η.app (op ⦋n⦌)).app a y, ?_⟩
  exact ConcreteCategory.congr_hom
    (congr_app (SimplicialObject.σ_naturality η i) a) y |>.symm

/-- Naturality on a finite latching stage. -/
def outerLatchingStageMap {X Y : SimplicialObject SSet.{u}}
    (η : X ⟶ Y) (n : ℕ) (r : Fin (n + 1)) :
    (outerLatchingStage X n r : SSet.{u}) ⟶ outerLatchingStage Y n r :=
  Subcomplex.lift
    ((outerLatchingStage X n r).ι ≫ η.app (op ⦋n + 1⦌))
    (by rintro a _ ⟨⟨x, hx⟩, rfl⟩
        exact outerLatchingStage_map_mem η n r a x hx)

@[reassoc (attr := simp)]
theorem outerLatchingStageMap_ι
    {X Y : SimplicialObject SSet.{u}} (η : X ⟶ Y)
    (n : ℕ) (r : Fin (n + 1)) :
    outerLatchingStageMap η n r ≫ (outerLatchingStage Y n r).ι =
      (outerLatchingStage X n r).ι ≫ η.app (op ⦋n + 1⦌) :=
  Subcomplex.lift_ι _ _

@[simp]
theorem outerLatchingStageMap_id
    (X : SimplicialObject SSet.{u}) (n : ℕ) (r : Fin (n + 1)) :
    outerLatchingStageMap (𝟙 X) n r = 𝟙 _ := by
  apply (cancel_mono (outerLatchingStage X n r).ι).mp
  simp [outerLatchingStageMap]

@[reassoc]
theorem outerLatchingStageMap_comp
    {X Y Z : SimplicialObject SSet.{u}} (η : X ⟶ Y) (θ : Y ⟶ Z)
    (n : ℕ) (r : Fin (n + 1)) :
    outerLatchingStageMap (η ≫ θ) n r =
      outerLatchingStageMap η n r ≫ outerLatchingStageMap θ n r := by
  apply (cancel_mono (outerLatchingStage Z n r).ι).mp
  simp [outerLatchingStageMap]

/-- Naturality on the union of degeneracies before `r`. -/
def outerLatchingStageBeforeMap {X Y : SimplicialObject SSet.{u}}
    (η : X ⟶ Y) (n : ℕ) (r : Fin (n + 1)) :
    (outerLatchingStageBefore X n r : SSet.{u}) ⟶
      outerLatchingStageBefore Y n r :=
  Subcomplex.lift
    ((outerLatchingStageBefore X n r).ι ≫ η.app (op ⦋n + 1⦌))
    (by rintro a _ ⟨⟨x, hx⟩, rfl⟩
        exact outerLatchingStageBefore_map_mem η n r a x hx)

@[reassoc (attr := simp)]
theorem outerLatchingStageBeforeMap_ι
    {X Y : SimplicialObject SSet.{u}} (η : X ⟶ Y)
    (n : ℕ) (r : Fin (n + 1)) :
    outerLatchingStageBeforeMap η n r ≫
        (outerLatchingStageBefore Y n r).ι =
      (outerLatchingStageBefore X n r).ι ≫
        η.app (op ⦋n + 1⦌) :=
  Subcomplex.lift_ι _ _

/-- Naturality on the source overlap in the latching pushout. -/
def outerLatchingStageSourceOverlapMap
    {X Y : SimplicialObject SSet.{u}} (η : X ⟶ Y)
    (n : ℕ) (r : Fin (n + 1)) :
    (outerLatchingStageSourceOverlap X n r : SSet.{u}) ⟶
      outerLatchingStageSourceOverlap Y n r :=
  Subcomplex.lift
    ((outerLatchingStageSourceOverlap X n r).ι ≫ η.app (op ⦋n⦌)) (by
      rintro a _ ⟨⟨x, hx⟩, rfl⟩
      rw [mem_outerLatchingStageSourceOverlap_iff] at hx ⊢
      obtain ⟨i, hi, y, hxy⟩ := hx
      refine ⟨i, hi, (η.app (op ⦋n⦌)).app a y, ?_⟩
      calc
        (Y.σ i).app a ((η.app (op ⦋n⦌)).app a y) =
            (η.app (op ⦋n + 1⦌)).app a ((X.σ i).app a y) :=
          (ConcreteCategory.congr_hom
            (congr_app (SimplicialObject.σ_naturality η i) a) y).symm
        _ = (η.app (op ⦋n + 1⦌)).app a ((X.σ r).app a x) :=
          congrArg ((η.app (op ⦋n + 1⦌)).app a) hxy
        _ = (Y.σ r).app a ((η.app (op ⦋n⦌)).app a x) :=
          ConcreteCategory.congr_hom
            (congr_app (SimplicialObject.σ_naturality η r) a) x)

@[reassoc (attr := simp)]
theorem outerLatchingStageSourceOverlapMap_ι
    {X Y : SimplicialObject SSet.{u}} (η : X ⟶ Y)
    (n : ℕ) (r : Fin (n + 1)) :
    outerLatchingStageSourceOverlapMap η n r ≫
        (outerLatchingStageSourceOverlap Y n r).ι =
      (outerLatchingStageSourceOverlap X n r).ι ≫
        η.app (op ⦋n⦌) :=
  Subcomplex.lift_ι _ _

@[simp]
theorem outerLatchingStageSourceOverlapMap_id
    (X : SimplicialObject SSet.{u}) (n : ℕ) (r : Fin (n + 1)) :
    outerLatchingStageSourceOverlapMap (𝟙 X) n r = 𝟙 _ := by
  apply (cancel_mono (outerLatchingStageSourceOverlap X n r).ι).mp
  simp

@[reassoc]
theorem outerLatchingStageSourceOverlapMap_comp
    {X Y Z : SimplicialObject SSet.{u}} (η : X ⟶ Y) (θ : Y ⟶ Z)
    (n : ℕ) (r : Fin (n + 1)) :
    outerLatchingStageSourceOverlapMap (η ≫ θ) n r =
      outerLatchingStageSourceOverlapMap η n r ≫
        outerLatchingStageSourceOverlapMap θ n r := by
  apply (cancel_mono (outerLatchingStageSourceOverlap Z n r).ι).mp
  simp

/-- Naturality on the newly attached degeneracy range. -/
def outerDegeneracyRangeMap {X Y : SimplicialObject SSet.{u}}
    (η : X ⟶ Y) (n : ℕ) (r : Fin (n + 1)) :
    (Subcomplex.range (X.σ r) : SSet.{u}) ⟶ Subcomplex.range (Y.σ r) :=
  Subcomplex.lift
    ((Subcomplex.range (X.σ r)).ι ≫ η.app (op ⦋n + 1⦌)) (by
      rintro a _ ⟨⟨x, hx⟩, rfl⟩
      obtain ⟨y, rfl⟩ := hx
      exact ⟨(η.app (op ⦋n⦌)).app a y,
        ConcreteCategory.congr_hom
          (congr_app (SimplicialObject.σ_naturality η r) a) y |>.symm⟩)

@[reassoc (attr := simp)]
theorem outerDegeneracyRangeMap_ι
    {X Y : SimplicialObject SSet.{u}} (η : X ⟶ Y)
    (n : ℕ) (r : Fin (n + 1)) :
    outerDegeneracyRangeMap η n r ≫ (Subcomplex.range (Y.σ r)).ι =
      (Subcomplex.range (X.σ r)).ι ≫
        η.app (op ⦋n + 1⦌) :=
  Subcomplex.lift_ι _ _

/-- Naturality on the finite-stage overlap. -/
def outerLatchingStageOverlapMap {X Y : SimplicialObject SSet.{u}}
    (η : X ⟶ Y) (n : ℕ) (r : Fin (n + 1)) :
    (outerLatchingStageOverlap X n r : SSet.{u}) ⟶
      outerLatchingStageOverlap Y n r :=
  Subcomplex.lift
    ((outerLatchingStageOverlap X n r).ι ≫
      η.app (op ⦋n + 1⦌)) (by
        rintro a _ ⟨⟨x, hxBefore, hxRange⟩, rfl⟩
        exact ⟨outerLatchingStageBefore_map_mem η n r a x hxBefore,
          by
            obtain ⟨y, rfl⟩ := hxRange
            exact ⟨(η.app (op ⦋n⦌)).app a y,
              ConcreteCategory.congr_hom
                (congr_app (SimplicialObject.σ_naturality η r) a) y |>.symm⟩⟩)

@[reassoc (attr := simp)]
theorem outerLatchingStageOverlapMap_ι
    {X Y : SimplicialObject SSet.{u}} (η : X ⟶ Y)
    (n : ℕ) (r : Fin (n + 1)) :
    outerLatchingStageOverlapMap η n r ≫
        (outerLatchingStageOverlap Y n r).ι =
      (outerLatchingStageOverlap X n r).ι ≫
        η.app (op ⦋n + 1⦌) :=
  Subcomplex.lift_ι _ _

@[reassoc]
theorem outerLatchingOverlap_before_naturality
    {X Y : SimplicialObject SSet.{u}} (η : X ⟶ Y)
    (n : ℕ) (r : Fin (n + 1)) :
    outerLatchingStageOverlapMap η n r ≫
        outerLatchingOverlapToBefore Y n r =
      outerLatchingOverlapToBefore X n r ≫
        outerLatchingStageBeforeMap η n r := by
  apply (cancel_mono (outerLatchingStageBefore Y n r).ι).mp
  simp

@[reassoc]
theorem outerLatchingOverlap_range_naturality
    {X Y : SimplicialObject SSet.{u}} (η : X ⟶ Y)
    (n : ℕ) (r : Fin (n + 1)) :
    outerLatchingStageOverlapMap η n r ≫
        outerLatchingOverlapToRange Y n r =
      outerLatchingOverlapToRange X n r ≫
        outerDegeneracyRangeMap η n r := by
  apply (cancel_mono (Subcomplex.range (Y.σ r)).ι).mp
  simp

@[reassoc]
theorem outerLatchingBefore_stage_naturality
    {X Y : SimplicialObject SSet.{u}} (η : X ⟶ Y)
    (n : ℕ) (r : Fin (n + 1)) :
    outerLatchingStageBeforeMap η n r ≫
        (Subcomplex.homOfLE (by
          rw [outerLatchingStage_eq_before_sup_range]
          exact le_sup_left) :
          (outerLatchingStageBefore Y n r : SSet.{u}) ⟶
            outerLatchingStage Y n r) =
      (Subcomplex.homOfLE (by
          rw [outerLatchingStage_eq_before_sup_range]
          exact le_sup_left) :
          (outerLatchingStageBefore X n r : SSet.{u}) ⟶
            outerLatchingStage X n r) ≫
        outerLatchingStageMap η n r := by
  apply (cancel_mono (outerLatchingStage Y n r).ι).mp
  simp

@[reassoc]
theorem outerLatchingRange_stage_naturality
    {X Y : SimplicialObject SSet.{u}} (η : X ⟶ Y)
    (n : ℕ) (r : Fin (n + 1)) :
    outerDegeneracyRangeMap η n r ≫
        (Subcomplex.homOfLE (by
          rw [outerLatchingStage_eq_before_sup_range]
          exact le_sup_right) :
          (Subcomplex.range (Y.σ r) : SSet.{u}) ⟶
            outerLatchingStage Y n r) =
      (Subcomplex.homOfLE (by
          rw [outerLatchingStage_eq_before_sup_range]
          exact le_sup_right) :
          (Subcomplex.range (X.σ r) : SSet.{u}) ⟶
            outerLatchingStage X n r) ≫
        outerLatchingStageMap η n r := by
  apply (cancel_mono (outerLatchingStage Y n r).ι).mp
  simp

/-- Naturality of the top leg of the source-overlap latching pushout. -/
@[reassoc]
theorem outerLatchingStageSource_top_naturality
    {X Y : SimplicialObject SSet.{u}} (η : X ⟶ Y)
    (n : ℕ) (r : Fin (n + 1)) :
    outerLatchingStageSourceOverlapMap η n r ≫
        (outerLatchingStageBefore Y n r).fromPreimage (Y.σ r) =
      (outerLatchingStageBefore X n r).fromPreimage (X.σ r) ≫
        outerLatchingStageBeforeMap η n r := by
  apply (cancel_mono (outerLatchingStageBefore Y n r).ι).mp
  simp only [Category.assoc, Subcomplex.fromPreimage_ι,
    outerLatchingStageSourceOverlapMap_ι_assoc,
    outerLatchingStageBeforeMap_ι]
  exact congrArg
    (fun f => (outerLatchingStageSourceOverlap X n r).ι ≫ f)
    (SimplicialObject.σ_naturality η r).symm

/-- Naturality of the left leg of the source-overlap latching pushout. -/
@[reassoc]
theorem outerLatchingStageSource_left_naturality
    {X Y : SimplicialObject SSet.{u}} (η : X ⟶ Y)
    (n : ℕ) (r : Fin (n + 1)) :
    outerLatchingStageSourceOverlapMap η n r ≫
        (outerLatchingStageSourceOverlap Y n r).ι =
      (outerLatchingStageSourceOverlap X n r).ι ≫
        η.app (op ⦋n⦌) :=
  outerLatchingStageSourceOverlapMap_ι η n r

/-- Naturality of the right leg of the source-overlap latching pushout. -/
@[reassoc]
theorem outerLatchingStageSource_right_naturality
    {X Y : SimplicialObject SSet.{u}} (η : X ⟶ Y)
    (n : ℕ) (r : Fin (n + 1)) :
    outerLatchingStageBeforeMap η n r ≫
        (Subcomplex.homOfLE (by
          rw [outerLatchingStage_eq_before_sup_range]
          exact le_sup_left) :
          (outerLatchingStageBefore Y n r : SSet.{u}) ⟶
            outerLatchingStage Y n r) =
      (Subcomplex.homOfLE (by
          rw [outerLatchingStage_eq_before_sup_range]
          exact le_sup_left) :
          (outerLatchingStageBefore X n r : SSet.{u}) ⟶
            outerLatchingStage X n r) ≫
        outerLatchingStageMap η n r :=
  outerLatchingBefore_stage_naturality η n r

/-- Naturality of the bottom leg of the source-overlap latching pushout. -/
@[reassoc]
theorem outerLatchingStageSource_bottom_naturality
    {X Y : SimplicialObject SSet.{u}} (η : X ⟶ Y)
    (n : ℕ) (r : Fin (n + 1)) :
    η.app (op ⦋n⦌) ≫ outerDegeneracyToLatchingStage Y n r =
      outerDegeneracyToLatchingStage X n r ≫
        outerLatchingStageMap η n r := by
  apply (cancel_mono (outerLatchingStage Y n r).ι).mp
  simp only [Category.assoc, outerDegeneracyToLatchingStage_ι,
    outerLatchingStageMap_ι]
  exact (SimplicialObject.σ_naturality η r).symm

/-- The degree-cell construction commutes with a map of bisimplicial sets. -/
@[reassoc]
theorem diagonalCellMap_naturality
    {X Y : SimplicialObject SSet.{u}} (η : X ⟶ Y) (n : ℕ) :
    (η.app (op ⦋n⦌) ⊗ₘ 𝟙 Δ[n]) ≫ diagonalCellMap Y n =
      diagonalCellMap X n ≫ simplicialDiagonalFunctor.map η := by
  ext a z
  rcases z with ⟨x, θ⟩
  change
    (Y.map (stdSimplex.objEquiv θ).op).app a
        ((η.app (op ⦋n⦌)).app a x) =
      (η.app a).app a
        ((X.map (stdSimplex.objEquiv θ).op).app a x)
  exact ConcreteCategory.congr_hom
    (congr_app (η.naturality (stdSimplex.objEquiv θ).op) a) x |>.symm

private theorem diagonalFiltration_map_mem
    {X Y : SimplicialObject SSet.{u}} (η : X ⟶ Y) (n : ℕ)
    (a : SimplexCategoryᵒᵖ) (z : (simplicialDiagonalFunctor.obj X).obj a)
    (hz : z ∈ (diagonalFiltration X n).obj a) :
    (simplicialDiagonalFunctor.map η).app a z ∈
      (diagonalFiltration Y n).obj a := by
  simp only [diagonalFiltration, Subfunctor.iSup_obj, Set.mem_iUnion,
    Subcomplex.range, Subfunctor.range_obj, Set.mem_range] at hz ⊢
  obtain ⟨p, hp, w, rfl⟩ := hz
  exact ⟨p, hp, (η.app (op ⦋p⦌) ⊗ₘ 𝟙 Δ[p]).app a w,
    ConcreteCategory.congr_hom
      (congr_app (diagonalCellMap_naturality η p) a) w⟩

/-- A map of bisimplicial sets restricts to every diagonal-filtration stage. -/
noncomputable def diagonalFiltrationNatMap
    {X Y : SimplicialObject SSet.{u}} (η : X ⟶ Y) (n : ℕ) :
    (diagonalFiltration X n : SSet.{u}) ⟶ diagonalFiltration Y n :=
  Subcomplex.lift
    ((diagonalFiltration X n).ι ≫ simplicialDiagonalFunctor.map η)
    (by rintro a _ ⟨⟨z, hz⟩, rfl⟩
        exact diagonalFiltration_map_mem η n a z hz)

@[reassoc (attr := simp)]
theorem diagonalFiltrationNatMap_ι
    {X Y : SimplicialObject SSet.{u}} (η : X ⟶ Y) (n : ℕ) :
    diagonalFiltrationNatMap η n ≫ (diagonalFiltration Y n).ι =
      (diagonalFiltration X n).ι ≫
        simplicialDiagonalFunctor.map η :=
  Subcomplex.lift_ι _ _

@[simp]
theorem diagonalFiltrationNatMap_id
    (X : SimplicialObject SSet.{u}) (n : ℕ) :
    diagonalFiltrationNatMap (𝟙 X) n = 𝟙 _ := by
  apply (cancel_mono (diagonalFiltration X n).ι).mp
  simp

@[reassoc]
theorem diagonalFiltrationNatMap_comp
    {X Y Z : SimplicialObject SSet.{u}} (η : X ⟶ Y) (θ : Y ⟶ Z)
    (n : ℕ) :
    diagonalFiltrationNatMap (η ≫ θ) n =
      diagonalFiltrationNatMap η n ≫ diagonalFiltrationNatMap θ n := by
  apply (cancel_mono (diagonalFiltration Z n).ι).mp
  simp

@[reassoc]
theorem diagonalFiltrationMap_naturality
    {X Y : SimplicialObject SSet.{u}} (η : X ⟶ Y)
    {n m : ℕ} (h : n ≤ m) :
    diagonalFiltrationNatMap η n ≫ diagonalFiltrationMap Y h =
      diagonalFiltrationMap X h ≫ diagonalFiltrationNatMap η m := by
  apply (cancel_mono (diagonalFiltration Y m).ι).mp
  simp [diagonalFiltrationMap]

set_option backward.isDefEq.respectTransparency false in
/-- Naturality on the union-product attachment domain. -/
def diagonalAttachmentDomainMap
    {X Y : SimplicialObject SSet.{u}} (η : X ⟶ Y) (n : ℕ) :
    (diagonalAttachmentDomain X n : SSet.{u}) ⟶
      diagonalAttachmentDomain Y n :=
  Subcomplex.lift
    ((diagonalAttachmentDomain X n).ι ≫
      (η.app (op ⦋n + 1⦌) ⊗ₘ 𝟙 Δ[n + 1])) (by
        rintro a _ ⟨⟨⟨x, s⟩, hx⟩, rfl⟩
        change ⟨x, s⟩ ∈ ((outerLatching X (n + 1)).unionProd
          (boundary (n + 1))).obj a at hx
        change ⟨(η.app (op ⦋n + 1⦌)).app a x, s⟩ ∈
          ((outerLatching Y (n + 1)).unionProd
            (boundary (n + 1))).obj a
        rw [Subcomplex.mem_unionProd_iff] at hx ⊢
        rcases hx with hs | hx
        · exact Or.inl hs
        · exact Or.inr (by
            change (η.app (op ⦋n + 1⦌)).app a x ∈
              (outerLatching Y (n + 1)).obj a
            exact ((outerLatchingMap η (n + 1)).app a ⟨x, hx⟩).2))

@[simp]
theorem diagonalAttachmentDomainMap_id
    (X : SimplicialObject SSet.{u}) (n : ℕ) :
    diagonalAttachmentDomainMap (𝟙 X) n = 𝟙 _ := by
  apply (cancel_mono (diagonalAttachmentDomain X n).ι).mp
  simp [diagonalAttachmentDomainMap]

@[reassoc]
theorem diagonalAttachmentDomainMap_comp
    {X Y Z : SimplicialObject SSet.{u}} (η : X ⟶ Y) (θ : Y ⟶ Z)
    (n : ℕ) :
    diagonalAttachmentDomainMap (η ≫ θ) n =
      diagonalAttachmentDomainMap η n ≫
        diagonalAttachmentDomainMap θ n := by
  apply (cancel_mono (diagonalAttachmentDomain Z n).ι).mp
  simp [diagonalAttachmentDomainMap]

@[reassoc (attr := simp)]
theorem diagonalAttachmentDomainMap_ι
    {X Y : SimplicialObject SSet.{u}} (η : X ⟶ Y) (n : ℕ) :
    diagonalAttachmentDomainMap η n ≫
        (diagonalAttachmentDomain Y n).ι =
      (diagonalAttachmentDomain X n).ι ≫
        (η.app (op ⦋n + 1⦌) ⊗ₘ 𝟙 Δ[n + 1]) :=
  Subcomplex.lift_ι _ _

@[reassoc]
theorem diagonalAttachmentTopMap_naturality
    {X Y : SimplicialObject SSet.{u}} (η : X ⟶ Y) (n : ℕ) :
    diagonalAttachmentDomainMap η n ≫ diagonalAttachmentTopMap Y n =
      diagonalAttachmentTopMap X n ≫ diagonalFiltrationNatMap η n := by
  apply (cancel_mono (diagonalFiltration Y n).ι).mp
  simp only [Category.assoc]
  rw [diagonalAttachmentTopMap_ι, diagonalFiltrationNatMap_ι,
    diagonalAttachmentDomainMap_ι_assoc,
    diagonalAttachmentTopMap_ι_assoc]
  simpa only [Category.assoc] using congrArg
    (fun z => (diagonalAttachmentDomain X n).ι ≫ z)
    (diagonalCellMap_naturality η (n + 1))

@[reassoc]
theorem diagonalCellToFiltrationSucc_naturality
    {X Y : SimplicialObject SSet.{u}} (η : X ⟶ Y) (n : ℕ) :
    (η.app (op ⦋n + 1⦌) ⊗ₘ 𝟙 Δ[n + 1]) ≫
        diagonalCellToFiltrationSucc Y n =
      diagonalCellToFiltrationSucc X n ≫
        diagonalFiltrationNatMap η (n + 1) := by
  apply (cancel_mono (diagonalFiltration Y (n + 1)).ι).mp
  simp only [Category.assoc]
  rw [diagonalCellToFiltrationSucc_ι, diagonalFiltrationNatMap_ι,
    diagonalCellToFiltrationSucc_ι_assoc]
  exact diagonalCellMap_naturality η (n + 1)

end SSet

end
