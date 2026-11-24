/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Data.Finset.Basic
public import MathlibExt.AlgebraicTopology.SimplexCategory.Reedy

/-!
# Actual partial epi-factor latching categories

For an original simplex map `α : ⦋m⦌ ⟶ ⦋d⦌`, retain precisely the objects of the original
opposite-simplex latching category through whose original proper epimorphism `α` factors.
The category is full: all original comparison triangles are retained. Their actual
residual factors are unique, and their complete naturality is the original epi equation.
-/

section

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MorphismProperty Simplicial

namespace SimplexCategory.PartialLatching

/-- The original simplex map factors through the actual original proper epi latching arrow. -/
def Factors {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌) :
    ObjectProperty (reedyOp.Latching (Opposite.op ⦋m⦌)) := fun a ↦
  ∃ β : (reedyOp.latchingSource a).unop ⟶ ⦋d⦌, (reedyOp.latchingArrow a).unop ≫ β = α

/-- The full original latching subcategory of all proper epi factorizations of the given map. -/
abbrev Index {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌) := (Factors α).FullSubcategory

/-- The exact inclusion retaining every original latching object and comparison triangle. -/
abbrev inclusion {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌) :
    Index α ⥤ reedyOp.Latching (Opposite.op ⦋m⦌) := (Factors α).ι

/-- The partial index retains the actual original opposite-simplex source. -/
abbrev source {m d : ℕ} {α : ⦋m⦌ ⟶ ⦋d⦌} (a : Index α) : SimplexCategoryᵒᵖ :=
  reedyOp.latchingSource a.obj

/-- The partial index retains the actual original opposite epi arrow. -/
def arrow {m d : ℕ} {α : ⦋m⦌ ⟶ ⦋d⦌} (a : Index α) : source a ⟶ Opposite.op ⦋m⦌ :=
  reedyOp.latchingArrow a.obj

/-- The partial index retains every actual original comparison triangle arrow. -/
def comparison {m d : ℕ} {α : ⦋m⦌ ⟶ ⦋d⦌} {a b : Index α} (f : a ⟶ b) :
    source a ⟶ source b := reedyOp.latchingComparison f.hom

/-- Every retained original latching arrow is an actual original simplex epimorphism. -/
instance arrow_epi {m d : ℕ} {α : ⦋m⦌ ⟶ ⦋d⦌} (a : Index α) : Epi (arrow a).unop :=
  (reedyOp_direct _).mp (reedyOp.latchingArrow_mem a.obj)

/-- Every retained original proper epi has strictly smaller original source degree. -/
theorem source_lt {m d : ℕ} {α : ⦋m⦌ ⟶ ⦋d⦌} (a : Index α) : (source a).unop.len < m :=
  a.obj.property

/-- The retained comparison triangle is the literal original latching triangle. -/
@[reassoc]
theorem comparison_arrow {m d : ℕ} {α : ⦋m⦌ ⟶ ⦋d⦌} {a b : Index α} (f : a ⟶ b) :
    comparison f ≫ arrow b = arrow a := reedyOp.latchingComparison_arrow f.hom

/-- The original residual simplex map of each retained proper epi factorization. -/
def factor {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌) (a : Index α) : (source a).unop ⟶ ⦋d⦌ :=
  a.property.choose

/-- The full original proper epi and residual map recover the unchanged original simplex map. -/
@[reassoc]
theorem factor_eq {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌) (a : Index α) :
    (arrow a).unop ≫ factor α a = α := a.property.choose_spec

/-- The original epi makes the complete residual factor unique. -/
theorem factor_unique {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌) (a : Index α)
    (β : (source a).unop ⟶ ⦋d⦌) (h : (arrow a).unop ≫ β = α) : β = factor α a :=
  (cancel_epi (arrow a).unop).mp (h.trans (factor_eq α a).symm)

/-- Every original comparison triangle retains its whole original residual factor equation. -/
theorem factor_naturality {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌) {a b : Index α} (f : a ⟶ b) :
    factor α b = (comparison f).unop ≫ factor α a := by
  apply (cancel_epi (arrow b).unop).mp
  rw [factor_eq]
  have ht : (arrow b).unop ≫ (comparison f).unop = (arrow a).unop := by
    rw [← unop_comp, comparison_arrow]
  rw [← Category.assoc, ht, factor_eq]

/-- The exact partial index is finite because its original latching category is finite. -/
instance finiteIndex {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌) : Finite (Index α) :=
  Finite.of_injective (fun a : Index α ↦ a.obj) (fun _ _ h ↦ ObjectProperty.FullSubcategory.ext h)

/-- All original retained triangle morphism types are finite. -/
instance finiteIndexHom {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌) (a b : Index α) : Finite (a ⟶ b) :=
  Finite.of_injective (fun f : a ⟶ b ↦ f.hom) (fun _ _ h ↦ ObjectProperty.hom_ext (Factors α) h)

/-- The full original partial factorization index is an actual finite category. -/
instance indexFinCategory {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌) : FinCategory (Index α) where
  fintypeObj := Fintype.ofFinite _
  fintypeHom _ _ := Fintype.ofFinite _

end SimplexCategory.PartialLatching

end
end
end

section



/-!
# Exact empty and full original partial epi boundaries

An isomorphism cannot factor through a proper original epi latching arrow. A collapse
to the zero simplex factors through every original latching arrow. These facts retain
the complete original categories, residual maps and comparison triangles.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits Simplicial

namespace SimplexCategory.PartialLatching

/-- An original simplex isomorphism has no proper original epi factorization. -/
instance indexIsEmpty_of_isIso {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌) [IsIso α] : IsEmpty (Index α) :=
  ⟨fun a ↦ by
    let _ : IsIso ((arrow a).unop ≫ factor α a) := (factor_eq α a).symm ▸ inferInstance
    let _ : Mono (arrow a).unop := mono_of_mono (arrow a).unop (factor α a)
    have hle : m ≤ (source a).unop.len := len_le_of_mono (arrow a).unop
    exact Nat.not_lt_of_ge hle (source_lt a)⟩

/-- The original collapse to zero factors through every actual original proper epi. -/
theorem factors_zero {m : ℕ} (α : ⦋m⦌ ⟶ ⦋0⦌)
    (a : reedyOp.Latching (Opposite.op ⦋m⦌)) : Factors α a :=
  ⟨SimplexCategory.const (reedyOp.latchingSource a).unop ⦋0⦌ 0,
    (eq_const_to_zero _).trans (eq_const_to_zero α).symm⟩

/-- The exact full-collapse partial category is the unchanged original complete latching category.
-/
def zeroIndexEquivalence {m : ℕ} (α : ⦋m⦌ ⟶ ⦋0⦌) :
    Index α ≌ reedyOp.Latching (Opposite.op ⦋m⦌) where
  functor := inclusion α
  inverse :=
    { obj a := ⟨a, factors_zero α a⟩
      map f := ObjectProperty.homMk f }
  unitIso := NatIso.ofComponents (fun a ↦ (Factors α).isoMk (Iso.refl a.obj))
  counitIso := Iso.refl _

/-- The original full-collapse inclusion is an actual equivalence on every original triangle. -/
instance zeroInclusion_isEquivalence {m : ℕ} (α : ⦋m⦌ ⟶ ⦋0⦌) :
    (inclusion α).IsEquivalence := (zeroIndexEquivalence α).isEquivalence_functor

end SimplexCategory.PartialLatching

end
end
end

section



/-!
# Original simplex epi factorizations and collapsed adjacent pairs

An original epimorphism determines its fibers by its collapsed adjacent pairs. A simplex
map factors through that same original epi exactly when it collapses those pairs. The
residual map is constructed from an actual simplex section, retaining the epi equation.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uA uB

open CategoryTheory Simplicial

namespace SimplexCategory

/-- A monotone finite map's equal-value fibers are determined by its adjacent equalities. -/
theorem respects_fibers_of_respects_adjacent {n : ℕ} {A : Type uA} {B : Type uB}
    [PartialOrder B] (g : Fin (n + 1) → B) (hg : Monotone g) (f : Fin (n + 1) → A)
    (h : ∀ p : Fin n, g p.castSucc = g p.succ → f p.castSucc = f p.succ) :
    ∀ x y, g x = g y → f x = f y := by
  have H : ∀ y : Fin (n + 1), ∀ x, x ≤ y → g x = g y → f x = f y := by
    intro y
    induction y using Fin.induction with
    | zero =>
      intro x hx _
      have he : x = 0 := le_antisymm hx (Fin.zero_le x)
      subst x
      rfl
    | succ p ih =>
      intro x hx hxy
      by_cases he : x = p.succ
      · subst x
        rfl
      · have hx' : x ≤ p.castSucc := by
          apply Fin.le_iff_val_le_val.mpr
          exact Nat.le_of_lt_succ (Fin.lt_def.mp (lt_of_le_of_ne hx he))
        have hp : p.castSucc ≤ p.succ := Fin.le_iff_val_le_val.mpr (Nat.le_succ p.val)
        have hm : g p.castSucc = g p.succ :=
          le_antisymm (hg hp) (hxy ▸ hg hx')
        exact (ih x hx' (hxy.trans hm.symm)).trans (h p hm)
  intro x y hxy
  rcases le_total x y with hle | hle
  · exact H y x hle hxy
  · exact (H x y hle hxy.symm).symm

/-- The exact original adjacent pairs collapsed by a simplex map. -/
def adjacentKernel {m : ℕ} {D : SimplexCategory} (α : ⦋m⦌ ⟶ D) : Finset (Fin m) :=
  Finset.univ.filter (fun p ↦ α.toOrderHom p.castSucc = α.toOrderHom p.succ)

/-- Membership retains the original two adjacent vertices and their original images. -/
@[simp]
theorem mem_adjacentKernel {m : ℕ} {D : SimplexCategory} (α : ⦋m⦌ ⟶ D) (p : Fin m) :
    p ∈ adjacentKernel α ↔ α.toOrderHom p.castSucc = α.toOrderHom p.succ := by
  simp [adjacentKernel]

/-- The full original epi factorization exists exactly when its adjacent kernel is retained. -/
theorem exists_factor_iff_adjacentKernel_subset {m : ℕ} {K D : SimplexCategory}
    (g : ⦋m⦌ ⟶ K) [Epi g] (α : ⦋m⦌ ⟶ D) :
    (∃ β : K ⟶ D, g ≫ β = α) ↔ adjacentKernel g ⊆ adjacentKernel α := by
  constructor
  · rintro ⟨β, rfl⟩ p hp
    apply (mem_adjacentKernel _ p).mpr
    exact congrArg β.toOrderHom ((mem_adjacentKernel g p).mp hp)
  · intro h
    let _ : IsSplitEpi g := isSplitEpi_of_epi g
    let s := section_ g
    have hf : ∀ x y, g.toOrderHom x = g.toOrderHom y → α.toOrderHom x = α.toOrderHom y :=
      respects_fibers_of_respects_adjacent g.toOrderHom g.toOrderHom.monotone α.toOrderHom
        (fun p hp ↦ (mem_adjacentKernel α p).mp (h ((mem_adjacentKernel g p).mpr hp)))
    refine ⟨s ≫ α, ?_⟩
    ext x
    have hs : g.toOrderHom (s.toOrderHom (g.toOrderHom x)) = g.toOrderHom x :=
      congr_toOrderHom_apply (IsSplitEpi.id g) (g.toOrderHom x)
    exact congrArg Fin.val (hf _ _ hs)

end SimplexCategory

end
end
end

section



/-!
# Original simplex insertion and duplication maps

Splitting one original source vertex also splits its original image vertex. The
resulting square retains both original codegeneracies and every original comparison.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Simplicial

namespace SimplexCategory.EpiInsertion

/-- The original codegeneracy subtracts one precisely above its original pivot. -/
theorem predAbove_val {n : ℕ} (p : Fin (n + 1)) (x : Fin (n + 2)) :
    (p.predAbove x).val = if p.val < x.val then x.val - 1 else x.val := by
  simp only [Fin.predAbove, Fin.lt_def, Fin.val_castSucc]
  split_ifs <;> rfl

/-- The original codegeneracy identifies only its pivot's two adjacent vertices. -/
theorem predAbove_eq_iff_of_le {n : ℕ} (p : Fin (n + 1))
    (x y : Fin (n + 2)) (hxy : x ≤ y) :
    p.predAbove x = p.predAbove y ↔ x = y ∨ x = p.castSucc ∧ y = p.succ := by
  have h := Fin.le_iff_val_le_val.mp hxy
  simp only [Fin.ext_iff, predAbove_val, Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> omega

/-- Removing the pivot preserves the original left vertex of each remaining adjacent pair. -/
theorem predAbove_shift_castSucc {n : ℕ} (p : Fin (n + 1)) (i : Fin n) :
    p.predAbove (p.succAbove i).castSucc = i.castSucc := by
  by_cases hi : i.castSucc < p
  · rw [Fin.succAbove_of_castSucc_lt _ _ hi]
    exact Fin.predAbove_castSucc_of_le p i.castSucc (le_of_lt hi)
  · have hi' : p ≤ i.castSucc := le_of_not_gt hi
    have hv : p.val ≤ i.val := hi'
    rw [Fin.succAbove_of_le_castSucc _ _ hi']
    apply Fin.ext
    rw [predAbove_val]
    simp only [Fin.val_castSucc, Fin.val_succ]
    rw [ite_eq_left (by omega : p.val < i.val + 1)]
    omega

/-- Removing the pivot preserves the original right vertex of each remaining adjacent pair. -/
theorem predAbove_shift_succ {n : ℕ} (p : Fin (n + 1)) (i : Fin n) :
    p.predAbove (p.succAbove i).succ = i.succ := by
  by_cases hi : i.castSucc < p
  · have hv : i.val < p.val := hi
    rw [Fin.succAbove_of_castSucc_lt _ _ hi]
    apply Fin.ext
    rw [predAbove_val]
    simp only [Fin.val_castSucc, Fin.val_succ]
    rw [ite_eq_right (by omega : ¬ p.val < i.val + 1)]
  · have hi' : p ≤ i.castSucc := le_of_not_gt hi
    have hv : p.val ≤ i.val := hi'
    rw [Fin.succAbove_of_le_castSucc _ _ hi']
    apply Fin.ext
    rw [predAbove_val]
    simp only [Fin.val_succ]
    rw [ite_eq_left (by omega : p.val < i.val + 1 + 1)]
    omega

/-- The original two pivot vertices are split on the two sides of the original image vertex. -/
def splitValue {n k : ℕ} (p : Fin (n + 1)) (h : Fin (n + 1) →o Fin (k + 1))
    (x : Fin (n + 2)) : Fin (k + 2) :=
  if x ≤ p.castSucc then (h (p.predAbove x)).castSucc else (h (p.predAbove x)).succ

/-- Splitting a source vertex and its original image is monotone on every original vertex. -/
theorem splitValue_monotone {n k : ℕ} (p : Fin (n + 1))
    (h : Fin (n + 1) →o Fin (k + 1)) : Monotone (splitValue p h) := by
  intro x y hxy
  have hh : h (p.predAbove x) ≤ h (p.predAbove y) :=
    h.monotone (p.predAboveOrderHom.monotone hxy)
  unfold splitValue
  split_ifs with hx hy hy
  · exact Fin.castSucc_le_castSucc_iff.mpr hh
  · apply Fin.le_iff_val_le_val.mpr
    have H := Fin.le_iff_val_le_val.mp hh
    simpa only [Fin.val_castSucc, Fin.val_succ] using H.trans (Nat.le_succ _)
  · exact (hx (hxy.trans hy)).elim
  · exact Fin.succ_le_succ_iff.mpr hh

/-- Collapsing the original inserted target vertex recovers the entire original source map. -/
theorem splitValue_square {n k : ℕ} (p : Fin (n + 1))
    (h : Fin (n + 1) →o Fin (k + 1)) (x : Fin (n + 2)) :
    (h p).predAbove (splitValue p h x) = h (p.predAbove x) := by
  unfold splitValue
  split_ifs with hx
  · have hq : p.predAbove x ≤ p := by
      have H := p.predAboveOrderHom.monotone hx
      change p.predAbove x ≤ p.predAbove p.castSucc at H
      simpa only [Fin.predAbove_castSucc_self] using H
    exact Fin.predAbove_castSucc_of_le _ _ (h.monotone hq)
  · have hx' : p.succ ≤ x := Fin.castSucc_lt_iff_succ_le.mp (lt_of_not_ge hx)
    have hq : p ≤ p.predAbove x := by
      have H := p.predAboveOrderHom.monotone hx'
      change p.predAbove p.succ ≤ p.predAbove x at H
      simpa only [Fin.predAbove_succ_self] using H
    exact Fin.predAbove_succ_of_le _ _ (h.monotone hq)

/-- The unchanged original map with one original vertex and image vertex split. -/
def liftAt {n k : ℕ} (p : Fin (n + 1)) (h : ⦋n⦌ ⟶ ⦋k⦌) : ⦋n + 1⦌ ⟶ ⦋k + 1⦌ :=
  mkHom ⟨splitValue p h.toOrderHom, splitValue_monotone p h.toOrderHom⟩

/-- The complete original codegeneracy square of the lifted simplex map. -/
theorem liftAt_square {n k : ℕ} (p : Fin (n + 1)) (h : ⦋n⦌ ⟶ ⦋k⦌) :
    liftAt p h ≫ σ (h.toOrderHom p) = σ p ≫ h := by
  ext x
  exact congrArg Fin.val (splitValue_square p h.toOrderHom x)

/-- The split map uses the actual original image at the left pivot vertex. -/
theorem liftAt_castSucc {n k : ℕ} (p : Fin (n + 1)) (h : ⦋n⦌ ⟶ ⦋k⦌) :
    (liftAt p h).toOrderHom p.castSucc = (h.toOrderHom p).castSucc := by
  simp [liftAt, splitValue, Fin.predAbove_castSucc_self]

/-- The split map uses the successor of the same actual image at the right pivot vertex. -/
theorem liftAt_succ {n k : ℕ} (p : Fin (n + 1)) (h : ⦋n⦌ ⟶ ⦋k⦌) :
    (liftAt p h).toOrderHom p.succ = (h.toOrderHom p).succ := by
  have H : ¬ p.succ ≤ p.castSucc := by simp [Fin.le_iff_val_le_val]
  simp [liftAt, splitValue, H, Fin.predAbove_succ_self]

/-- The original inserted source pair is not collapsed by the lifted map. -/
theorem not_mem_adjacentKernel_liftAt {n k : ℕ} (p : Fin (n + 1))
    (h : ⦋n⦌ ⟶ ⦋k⦌) : p ∉ adjacentKernel (liftAt p h) := by
  rw [mem_adjacentKernel, liftAt_castSucc, liftAt_succ]
  exact (Fin.ne_of_lt (h.toOrderHom p).castSucc_lt_succ)

/-- Every other original adjacent kernel pair shifts through the original source insertion. -/
theorem mem_adjacentKernel_liftAt_shift {n k : ℕ} (p : Fin (n + 1))
    (h : ⦋n⦌ ⟶ ⦋k⦌) (i : Fin n) :
    p.succAbove i ∈ adjacentKernel (liftAt p h) ↔ i ∈ adjacentKernel h := by
  rw [mem_adjacentKernel, mem_adjacentKernel]
  change splitValue p h.toOrderHom (p.succAbove i).castSucc =
    splitValue p h.toOrderHom (p.succAbove i).succ ↔ _
  unfold splitValue
  rw [predAbove_shift_castSucc, predAbove_shift_succ]
  by_cases hi : i.castSucc < p
  · have hv : i.val < p.val := hi
    have hl : (p.succAbove i).castSucc ≤ p.castSucc := by
      rw [Fin.succAbove_of_castSucc_lt _ _ hi]
      exact Fin.castSucc_le_castSucc_iff.mpr (le_of_lt hi)
    have hr : (p.succAbove i).succ ≤ p.castSucc := by
      rw [Fin.succAbove_of_castSucc_lt _ _ hi]
      change i.val + 1 ≤ p.val
      omega
    rw [ite_eq_left hl, ite_eq_left hr, Fin.castSucc_inj]
  · have hi' : p ≤ i.castSucc := le_of_not_gt hi
    have hv : p.val ≤ i.val := hi'
    have hl : ¬ (p.succAbove i).castSucc ≤ p.castSucc := by
      rw [Fin.succAbove_of_le_castSucc _ _ hi']
      change ¬ i.val + 1 ≤ p.val
      omega
    have hr : ¬ (p.succAbove i).succ ≤ p.castSucc := by
      rw [Fin.succAbove_of_le_castSucc _ _ hi']
      change ¬ i.val + 1 + 1 ≤ p.val
      omega
    rw [ite_eq_right hl, ite_eq_right hr, Fin.succ_inj]

/-- The original codegeneracy has precisely its one actual collapsed adjacent pair. -/
theorem adjacentKernel_sigma {n : ℕ} (p : Fin (n + 1)) : adjacentKernel (σ p) = {p} := by
  ext i
  rw [mem_adjacentKernel, Finset.mem_singleton]
  change p.predAbove i.castSucc = p.predAbove i.succ ↔ i = p
  rw [predAbove_eq_iff_of_le p _ _ i.castSucc_le_succ]
  constructor
  · rintro (h | ⟨h, _⟩)
    · exact (Fin.ne_of_lt i.castSucc_lt_succ h).elim
    · exact Fin.castSucc_injective _ h
  · rintro rfl
    exact Or.inr ⟨rfl, rfl⟩

/-- An original epi moves by at most one at each original adjacent source pair. -/
theorem epi_adjacent_step {m : ℕ} {K : SimplexCategory} (α : ⦋m⦌ ⟶ K) [Epi α]
    (p : Fin m) :
    (α.toOrderHom p.succ).val ≤ (α.toOrderHom p.castSucc).val + 1 := by
  by_contra hs
  let y : Fin (K.len + 1) := ⟨(α.toOrderHom p.castSucc).val + 1, by
    have H := (α.toOrderHom p.succ).isLt
    omega⟩
  obtain ⟨x, hx⟩ := (epi_iff_surjective.mp (inferInstance : Epi α)) y
  have hv : (α.toOrderHom x).val = (α.toOrderHom p.castSucc).val + 1 :=
    congrArg Fin.val hx
  by_cases hxp : x ≤ p.castSucc
  · have H := Fin.le_iff_val_le_val.mp (α.toOrderHom.monotone hxp)
    omega
  · have hxp' : p.succ ≤ x := Fin.castSucc_lt_iff_succ_le.mp (lt_of_not_ge hxp)
    have H := Fin.le_iff_val_le_val.mp (α.toOrderHom.monotone hxp')
    omega

/-- A noncollapsed original epi pair moves by exactly one original target vertex. -/
theorem epi_adjacent_step_eq {m : ℕ} {K : SimplexCategory} (α : ⦋m⦌ ⟶ K) [Epi α]
    (p : Fin m) (hp : p ∉ adjacentKernel α) :
    (α.toOrderHom p.succ).val = (α.toOrderHom p.castSucc).val + 1 := by
  have H := epi_adjacent_step α p
  have hm := Fin.le_iff_val_le_val.mp (α.toOrderHom.monotone p.castSucc_le_succ)
  have hn : (α.toOrderHom p.castSucc).val ≠ (α.toOrderHom p.succ).val := by
    intro he
    exact hp ((mem_adjacentKernel α p).mpr (Fin.ext he))
  omega

end SimplexCategory.EpiInsertion

end
end
end

section



/-!
# Original epi collapse at one missing adjacent kernel pair

The new target pivot is the value of the original epi at the original left
source vertex. Both actual codegeneracies and the unique original residual epi
retain their whole square. All other original kernel pairs shift by `succAbove`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Simplicial

namespace SimplexCategory.EpiInsertion

/-- The original left image is a valid target insertion pivot whenever the pair is not collapsed. -/
def targetIndex {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) (p : Fin (n + 1))
    (hp : p ∉ adjacentKernel α) : Fin (d + 1) :=
  ⟨(α.toOrderHom p.castSucc).val, by
    have H : (α.toOrderHom p.succ).val < d + 2 := (α.toOrderHom p.succ).isLt
    have hm : (α.toOrderHom p.castSucc).val ≤ (α.toOrderHom p.succ).val :=
      α.toOrderHom.monotone p.castSucc_le_succ
    have hn : (α.toOrderHom p.castSucc).val ≠ (α.toOrderHom p.succ).val := by
      intro he
      exact hp ((mem_adjacentKernel α p).mpr (Fin.ext he))
    omega⟩

/-- The target pivot is the exact original left vertex value. -/
theorem targetIndex_castSucc {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌)
    (p : Fin (n + 1)) (hp : p ∉ adjacentKernel α) :
    (targetIndex α p hp).castSucc = α.toOrderHom p.castSucc := by
  apply Fin.ext
  rfl

/-- For the original epi, the target pivot's successor is the exact original right value. -/
theorem targetIndex_succ {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α]
    (p : Fin (n + 1)) (hp : p ∉ adjacentKernel α) :
    (targetIndex α p hp).succ = α.toOrderHom p.succ := by
  apply Fin.ext
  exact (epi_adjacent_step_eq α p hp).symm

/-- The original epi followed by the actual target codegeneracy at its original image pivot. -/
def plus {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) (p : Fin (n + 1))
    (hp : p ∉ adjacentKernel α) : ⦋n + 1⦌ ⟶ ⦋d⦌ :=
  α ≫ σ (targetIndex α p hp)

/-- The new full source map remains an original simplex epimorphism. -/
instance plus_epi {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α]
    (p : Fin (n + 1)) (hp : p ∉ adjacentKernel α) : Epi (plus α p hp) := by
  dsimp only [plus]
  infer_instance

/-- The one original missing source collapse occurs in the actual new epi. -/
theorem mem_adjacentKernel_plus {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α]
    (p : Fin (n + 1)) (hp : p ∉ adjacentKernel α) : p ∈ adjacentKernel (plus α p hp) := by
  rw [mem_adjacentKernel]
  change (targetIndex α p hp).predAbove (α.toOrderHom p.castSucc) =
    (targetIndex α p hp).predAbove (α.toOrderHom p.succ)
  rw [← targetIndex_castSucc α p hp, ← targetIndex_succ α p hp]
  simp only [Fin.predAbove_castSucc_self, Fin.predAbove_succ_self]

/-- A monotone map has only one transition between the same two distinct adjacent images. -/
theorem unique_adjacent_transition {m : ℕ} {K : SimplexCategory} (α : ⦋m⦌ ⟶ K)
    (p : Fin m) (hp : p ∉ adjacentKernel α) (i : Fin m)
    (hl : α.toOrderHom i.castSucc = α.toOrderHom p.castSucc)
    (hr : α.toOrderHom i.succ = α.toOrderHom p.succ) : i = p := by
  by_contra hi
  have hm := α.toOrderHom.monotone p.castSucc_le_succ
  have hn : α.toOrderHom p.castSucc ≠ α.toOrderHom p.succ :=
    fun h ↦ hp ((mem_adjacentKernel α p).mpr h)
  have hs : α.toOrderHom p.castSucc < α.toOrderHom p.succ := lt_of_le_of_ne hm hn
  rcases lt_or_gt_of_ne hi with h | h
  · have hsource : i.succ ≤ p.castSucc := by
      change i.val + 1 ≤ p.val
      exact Nat.succ_le_of_lt h
    have H := α.toOrderHom.monotone hsource
    rw [hr] at H
    exact (not_le_of_gt hs H)
  · have hsource : p.succ ≤ i.castSucc := by
      change p.val + 1 ≤ i.val
      exact Nat.succ_le_of_lt h
    have H := α.toOrderHom.monotone hsource
    rw [hl] at H
    exact (not_le_of_gt hs H)

/-- The actual new epi adds exactly the one original missing source collapse. -/
theorem adjacentKernel_plus {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α]
    (p : Fin (n + 1)) (hp : p ∉ adjacentKernel α) :
    adjacentKernel (plus α p hp) = insert p (adjacentKernel α) := by
  ext i
  rw [mem_adjacentKernel, Finset.mem_insert, mem_adjacentKernel]
  change (targetIndex α p hp).predAbove (α.toOrderHom i.castSucc) =
    (targetIndex α p hp).predAbove (α.toOrderHom i.succ) ↔
    i = p ∨ α.toOrderHom i.castSucc = α.toOrderHom i.succ
  rw [predAbove_eq_iff_of_le _ _ _ (α.toOrderHom.monotone i.castSucc_le_succ)]
  constructor
  · rintro (he | ⟨hl, hr⟩)
    · exact Or.inr he
    · exact Or.inl (unique_adjacent_transition α p hp i
        (hl.trans (targetIndex_castSucc α p hp))
        (hr.trans (targetIndex_succ α p hp)))
  · rintro (rfl | he)
    · exact Or.inr ⟨(targetIndex_castSucc α i hp).symm, (targetIndex_succ α i hp).symm⟩
    · exact Or.inl he

/-- The new original epi factors through the original source codegeneracy. -/
theorem exists_res {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α]
    (p : Fin (n + 1)) (hp : p ∉ adjacentKernel α) :
    ∃ β : ⦋n⦌ ⟶ ⦋d⦌, σ p ≫ β = plus α p hp := by
  apply (exists_factor_iff_adjacentKernel_subset (σ p) (plus α p hp)).mpr
  rw [adjacentKernel_sigma]
  intro i hi
  have he : i = p := Finset.mem_singleton.mp hi
  subst i
  exact mem_adjacentKernel_plus α p hp

/-- The original unique residual simplex map after collapsing that original source pair. -/
def res {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α]
    (p : Fin (n + 1)) (hp : p ∉ adjacentKernel α) : ⦋n⦌ ⟶ ⦋d⦌ :=
  (exists_res α p hp).choose

/-- The residual map retains both whole original codegeneracies and the original source epi. -/
theorem res_square {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α]
    (p : Fin (n + 1)) (hp : p ∉ adjacentKernel α) :
    σ p ≫ res α p hp = α ≫ σ (targetIndex α p hp) :=
  (exists_res α p hp).choose_spec

/-- The original source epi makes the complete residual map unique. -/
theorem res_unique {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α]
    (p : Fin (n + 1)) (hp : p ∉ adjacentKernel α) (β : ⦋n⦌ ⟶ ⦋d⦌)
    (hβ : σ p ≫ β = α ≫ σ (targetIndex α p hp)) : β = res α p hp :=
  (cancel_epi (σ p)).mp (hβ.trans (res_square α p hp).symm)

/-- The original residual map remains an actual epimorphism. -/
instance res_epi {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α]
    (p : Fin (n + 1)) (hp : p ∉ adjacentKernel α) : Epi (res α p hp) := by
  have h : Epi (σ p ≫ res α p hp) := by
    rw [res_square]
    infer_instance
  exact CategoryTheory.epi_of_epi (σ p) (res α p hp)

/-- The original source codegeneracy carries every remaining pair to the original residual pair. -/
theorem mem_adjacentKernel_sigma_shift {n : ℕ} {K : SimplexCategory}
    (p : Fin (n + 1)) (β : ⦋n⦌ ⟶ K) (i : Fin n) :
    p.succAbove i ∈ adjacentKernel (σ p ≫ β) ↔ i ∈ adjacentKernel β := by
  rw [mem_adjacentKernel, mem_adjacentKernel]
  change β.toOrderHom (p.predAbove (p.succAbove i).castSucc) =
    β.toOrderHom (p.predAbove (p.succAbove i).succ) ↔ _
  rw [predAbove_shift_castSucc, predAbove_shift_succ]

/-- Every residual adjacent collapse is precisely the shifted original collapse. -/
theorem mem_adjacentKernel_res_shift {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α]
    (p : Fin (n + 1)) (hp : p ∉ adjacentKernel α) (i : Fin n) :
    i ∈ adjacentKernel (res α p hp) ↔ p.succAbove i ∈ adjacentKernel α := by
  have h := mem_adjacentKernel_sigma_shift p (res α p hp) i
  change p.succAbove i ∈ adjacentKernel (σ p ≫ res α p hp) ↔ _ at h
  rw [res_square] at h
  change p.succAbove i ∈ adjacentKernel (plus α p hp) ↔ _ at h
  rw [adjacentKernel_plus] at h
  simpa only [Finset.mem_insert, Fin.succAbove_ne, false_or] using h.symm

end SimplexCategory.EpiInsertion

end
end
end

section



/-!
# Original epi lifts and their complete comparison triangles

The actual source and target vertex insertions preserve original epimorphisms,
identities and composition. Collapsing and lifting a noncollapsed original epi
recovers the same original morphism at every vertex.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Simplicial

namespace SimplexCategory.EpiInsertion

/-- Being left of the inserted target vertex is exactly being left of the original source pivot. -/
theorem splitValue_target_left_iff {n k : ℕ} (p : Fin (n + 1))
    (h : Fin (n + 1) →o Fin (k + 1)) (x : Fin (n + 2)) :
    splitValue p h x ≤ (h p).castSucc ↔ x ≤ p.castSucc := by
  by_cases hx : x ≤ p.castSucc
  · have H := p.predAboveOrderHom.monotone hx
    change p.predAbove x ≤ p.predAbove p.castSucc at H
    rw [Fin.predAbove_castSucc_self] at H
    have ht : splitValue p h x ≤ (h p).castSucc := by
      rw [splitValue, ite_eq_left hx]
      exact Fin.castSucc_le_castSucc_iff.mpr (h.monotone H)
    exact ⟨fun _ ↦ hx, fun _ ↦ ht⟩
  · have hx' : p.succ ≤ x := Fin.castSucc_lt_iff_succ_le.mp (lt_of_not_ge hx)
    have H := p.predAboveOrderHom.monotone hx'
    change p.predAbove p.succ ≤ p.predAbove x at H
    rw [Fin.predAbove_succ_self] at H
    have hv : (h p).val ≤ (h (p.predAbove x)).val := h.monotone H
    have ht : ¬ splitValue p h x ≤ (h p).castSucc := by
      rw [splitValue, ite_eq_right hx]
      change ¬ (h (p.predAbove x)).val + 1 ≤ (h p).val
      omega
    exact ⟨fun h ↦ (ht h).elim, fun h ↦ (hx h).elim⟩

/-- Every original pre-pivot source vertex keeps its unchanged original image. -/
theorem liftAt_before {n k : ℕ} (p : Fin (n + 1)) (h : ⦋n⦌ ⟶ ⦋k⦌)
    (x : Fin (n + 1)) (hx : x ≤ p) :
    (liftAt p h).toOrderHom x.castSucc = (h.toOrderHom x).castSucc := by
  change splitValue p h.toOrderHom x.castSucc = _
  rw [splitValue, ite_eq_left (Fin.castSucc_le_castSucc_iff.mpr hx),
    Fin.predAbove_castSucc_of_le p x hx]

/-- Every original post-pivot source vertex keeps the successor of its unchanged image. -/
theorem liftAt_after {n k : ℕ} (p : Fin (n + 1)) (h : ⦋n⦌ ⟶ ⦋k⦌)
    (x : Fin (n + 1)) (hx : p ≤ x) :
    (liftAt p h).toOrderHom x.succ = (h.toOrderHom x).succ := by
  have hv : p.val ≤ x.val := hx
  have ht : ¬ x.succ ≤ p.castSucc := by
    change ¬ x.val + 1 ≤ p.val
    omega
  change splitValue p h.toOrderHom x.succ = _
  rw [splitValue, ite_eq_right ht, Fin.predAbove_succ_of_le p x hx]

/-- Splitting retains the original surjectivity on both sides of the same original target pivot. -/
theorem liftAt_surjective {n k : ℕ} (p : Fin (n + 1)) (h : ⦋n⦌ ⟶ ⦋k⦌)
    (hs : Function.Surjective h.toOrderHom) : Function.Surjective (liftAt p h).toOrderHom := by
  intro y
  by_cases hy : y ≤ (h.toOrderHom p).castSucc
  · by_cases he : y = (h.toOrderHom p).castSucc
    · exact ⟨p.castSucc, (liftAt_castSucc p h).trans he.symm⟩
    · have hv : y.val ≤ (h.toOrderHom p).val := hy
      have hn : y.val ≠ (h.toOrderHom p).val := fun e ↦ he (Fin.ext e)
      have hlt : y.val < (h.toOrderHom p).val := lt_of_le_of_ne hv hn
      let z : Fin (k + 1) := ⟨y.val, hlt.trans (h.toOrderHom p).isLt⟩
      obtain ⟨x, hx⟩ := hs z
      have hxp : x ≤ p := by
        by_contra H
        have H' := h.toOrderHom.monotone (le_of_lt (lt_of_not_ge H))
        have hv' : (h.toOrderHom p).val ≤ (h.toOrderHom x).val := H'
        have he' : (h.toOrderHom x).val = y.val := congrArg Fin.val hx
        omega
      refine ⟨x.castSucc, (liftAt_before p h x hxp).trans ?_⟩
      rw [hx]
      apply Fin.ext
      rfl
  · by_cases he : y = (h.toOrderHom p).succ
    · exact ⟨p.succ, (liftAt_succ p h).trans he.symm⟩
    · have hv : (h.toOrderHom p).val < y.val := lt_of_not_ge hy
      have hn : y.val ≠ (h.toOrderHom p).val + 1 := fun e ↦ he (Fin.ext e)
      have hlt : (h.toOrderHom p).val + 1 < y.val := by omega
      let z : Fin (k + 1) := ⟨y.val - 1, by
        have H : y.val < k + 2 := y.isLt
        omega⟩
      obtain ⟨x, hx⟩ := hs z
      have hxp : p ≤ x := by
        by_contra H
        have H' := h.toOrderHom.monotone (le_of_lt (lt_of_not_ge H))
        have hv' : (h.toOrderHom x).val ≤ (h.toOrderHom p).val := H'
        have he' : (h.toOrderHom x).val = y.val - 1 := congrArg Fin.val hx
        omega
      refine ⟨x.succ, (liftAt_after p h x hxp).trans ?_⟩
      rw [hx]
      apply Fin.ext
      change (y.val - 1) + 1 = y.val
      omega

/-- The lifted original epi remains an actual simplex epimorphism. -/
instance liftAt_epi {n k : ℕ} (p : Fin (n + 1)) (h : ⦋n⦌ ⟶ ⦋k⦌) [Epi h] :
    Epi (liftAt p h) :=
  epi_iff_surjective.mpr (liftAt_surjective p h (epi_iff_surjective.mp inferInstance))

/-- Splitting an original map and a comparison retains their whole original composition. -/
theorem splitValue_comp {n k l : ℕ} (p : Fin (n + 1))
    (h : Fin (n + 1) →o Fin (k + 1)) (v : Fin (k + 1) →o Fin (l + 1))
    (x : Fin (n + 2)) :
    splitValue (h p) v (splitValue p h x) = splitValue p (v.comp h) x := by
  change (if splitValue p h x ≤ (h p).castSucc then
      (v ((h p).predAbove (splitValue p h x))).castSucc else
      (v ((h p).predAbove (splitValue p h x))).succ) = _
  rw [splitValue_square]
  by_cases hx : x ≤ p.castSucc
  · have ht := (splitValue_target_left_iff p h x).mpr hx
    rw [ite_eq_left ht, splitValue, ite_eq_left hx]
    rfl
  · have ht : ¬ splitValue p h x ≤ (h p).castSucc :=
      fun H ↦ hx ((splitValue_target_left_iff p h x).mp H)
    rw [ite_eq_right ht, splitValue, ite_eq_right hx]
    rfl

/-- Every lifted original comparison triangle keeps the same original composite morphism. -/
theorem liftAt_comp {n k l : ℕ} (p : Fin (n + 1)) (h : ⦋n⦌ ⟶ ⦋k⦌)
    (v : ⦋k⦌ ⟶ ⦋l⦌) :
    liftAt p h ≫ liftAt (h.toOrderHom p) v = liftAt p (h ≫ v) := by
  ext x
  exact congrArg Fin.val (splitValue_comp p h.toOrderHom v.toOrderHom x)

/-- The complete original identity stays the identity after inserting the original pivot. -/
theorem liftAt_id {n : ℕ} (p : Fin (n + 1)) : liftAt p (𝟙 ⦋n⦌) = 𝟙 ⦋n + 1⦌ := by
  ext x
  change (splitValue p OrderHom.id x).val = x.val
  unfold splitValue
  by_cases hx : x ≤ p.castSucc
  · have hv : x.val ≤ p.val := hx
    rw [ite_eq_left hx]
    change (p.predAbove x).val = x.val
    rw [predAbove_val, ite_eq_right (by omega : ¬ p.val < x.val)]
  · have hv : p.val < x.val := lt_of_not_ge hx
    rw [ite_eq_right hx]
    change (p.predAbove x).val + 1 = x.val
    rw [predAbove_val, ite_eq_left hv]
    omega

/-- The whole original epi triangle is retained by both original image-pivot insertions. -/
theorem liftAt_triangle {n k l : ℕ} (p : Fin (n + 1))
    (h' : ⦋n⦌ ⟶ ⦋k⦌) (h : ⦋n⦌ ⟶ ⦋l⦌) (v : ⦋k⦌ ⟶ ⦋l⦌) (hv : h' ≫ v = h) :
    liftAt p h' ≫ liftAt (h'.toOrderHom p) v = liftAt p h := by
  rw [liftAt_comp, hv]

/-- The actual original residual map sends the original pivot to the original target pivot. -/
theorem res_pivot {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α]
    (p : Fin (n + 1)) (hp : p ∉ adjacentKernel α) :
    (res α p hp).toOrderHom p = targetIndex α p hp := by
  have H := congr_toOrderHom_apply (res_square α p hp) p.castSucc
  change (res α p hp).toOrderHom (p.predAbove p.castSucc) =
    (targetIndex α p hp).predAbove (α.toOrderHom p.castSucc) at H
  rw [Fin.predAbove_castSucc_self, ← targetIndex_castSucc α p hp,
    Fin.predAbove_castSucc_self] at H
  exact H

/-- Collapsing and lifting recovers every vertex of the same original noncollapsed epi. -/
theorem liftAt_res {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α]
    (p : Fin (n + 1)) (hp : p ∉ adjacentKernel α) : liftAt p (res α p hp) = α := by
  have hs := liftAt_square p (res α p hp)
  rw [res_pivot α p hp, res_square α p hp] at hs
  ext x
  have H := congrArg Fin.val (congr_toOrderHom_apply hs x)
  change ((targetIndex α p hp).predAbove ((liftAt p (res α p hp)).toOrderHom x)).val =
    ((targetIndex α p hp).predAbove (α.toOrderHom x)).val at H
  rw [predAbove_val, predAbove_val] at H
  by_cases hx : x ≤ p.castSucc
  · have hg := (splitValue_target_left_iff p (res α p hp).toOrderHom x).mpr hx
    change (liftAt p (res α p hp)).toOrderHom x ≤
      ((res α p hp).toOrderHom p).castSucc at hg
    rw [res_pivot α p hp] at hg
    have ha := α.toOrderHom.monotone hx
    rw [← targetIndex_castSucc α p hp] at ha
    have hgv : ((liftAt p (res α p hp)).toOrderHom x).val ≤ (targetIndex α p hp).val := hg
    have hav : (α.toOrderHom x).val ≤ (targetIndex α p hp).val := ha
    rw [ite_eq_right (by omega : ¬ (targetIndex α p hp).val <
      ((liftAt p (res α p hp)).toOrderHom x).val),
      ite_eq_right (by omega : ¬ (targetIndex α p hp).val < (α.toOrderHom x).val)] at H
    exact H
  · have hg : ¬ (liftAt p (res α p hp)).toOrderHom x ≤
        ((res α p hp).toOrderHom p).castSucc :=
      fun hg ↦ hx ((splitValue_target_left_iff p (res α p hp).toOrderHom x).mp hg)
    rw [res_pivot α p hp] at hg
    have hx' : p.succ ≤ x := Fin.castSucc_lt_iff_succ_le.mp (lt_of_not_ge hx)
    have ha := α.toOrderHom.monotone hx'
    rw [← targetIndex_succ α p hp] at ha
    have hgv : (targetIndex α p hp).val < ((liftAt p (res α p hp)).toOrderHom x).val :=
      lt_of_not_ge hg
    have hav : (targetIndex α p hp).val + 1 ≤ (α.toOrderHom x).val := ha
    rw [ite_eq_left hgv, ite_eq_left (by omega :
      (targetIndex α p hp).val < (α.toOrderHom x).val)] at H
    omega

end SimplexCategory.EpiInsertion

end
end
end

section



/-!
# Original epi-factor category insertions

The direct inclusion, residual composition and original vertex lift act on the
actual full opposite-simplex latching subcategories. Every original epi, residual
factor and comparison triangle is retained.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Simplicial
open SimplexCategory.EpiInsertion

namespace SimplexCategory.PartialLatching.Insertion

/-- Construct an actual original latching object from its whole proper epi factorization. -/
@[implicit_reducible]
def mk {m d : ℕ} {K : SimplexCategory} (α : ⦋m⦌ ⟶ ⦋d⦌) (g : ⦋m⦌ ⟶ K)
    [Epi g] (hk : K.len < m) (β : K ⟶ ⦋d⦌) (hβ : g ≫ β = α) : Index α :=
  ⟨⟨Over.mk ⟨g.op, (reedyOp_direct g.op).mpr inferInstance⟩, hk⟩, ⟨β, hβ⟩⟩

/-- The constructed object has exactly the original target simplex as its opposite source. -/
theorem source_mk {m d : ℕ} {K : SimplexCategory} (α : ⦋m⦌ ⟶ ⦋d⦌)
    (g : ⦋m⦌ ⟶ K) [Epi g] (hk : K.len < m) (β : K ⟶ ⦋d⦌) (hβ : g ≫ β = α) :
    source (mk α g hk β hβ) = Opposite.op K := rfl

/-- The constructed object keeps the exact original epi as its original latching arrow. -/
theorem arrow_mk {m d : ℕ} {K : SimplexCategory} (α : ⦋m⦌ ⟶ ⦋d⦌)
    (g : ⦋m⦌ ⟶ K) [Epi g] (hk : K.len < m) (β : K ⟶ ⦋d⦌) (hβ : g ≫ β = α) :
    arrow (mk α g hk β hβ) = g.op := rfl

/-- The whole original proper epi makes each original comparison triangle unique. -/
theorem hom_ext {m d : ℕ} {α : ⦋m⦌ ⟶ ⦋d⦌} {a b : Index α} {f g : a ⟶ b}
    (h : comparison f = comparison g) : f = g := by
  apply ObjectProperty.hom_ext (Factors α)
  apply ObjectProperty.hom_ext (reedyOp.latchingObjects (Opposite.op ⦋m⦌))
  apply CostructuredArrow.hom_ext _ _
  exact WideSubcategory.hom_ext _ h

/-- The full original epi-factor category is thin by original epi cancellation. -/
instance homSubsingleton {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌) (a b : Index α) :
    Subsingleton (a ⟶ b) where
  allEq f g := hom_ext (by
    apply Quiver.Hom.unop_inj
    apply (cancel_epi (arrow b).unop).mp
    have hf : (arrow b).unop ≫ (comparison f).unop = (arrow a).unop := by
      rw [← unop_comp, comparison_arrow]
    have hg : (arrow b).unop ≫ (comparison g).unop = (arrow a).unop := by
      rw [← unop_comp, comparison_arrow]
    exact hf.trans hg.symm)

/-- Construct a genuine original comparison retaining its whole original triangle. -/
@[implicit_reducible]
def homMk {m d : ℕ} {α : ⦋m⦌ ⟶ ⦋d⦌} {a b : Index α}
    (v : source a ⟶ source b) (hv : v ≫ arrow b = arrow a) : a ⟶ b := by
  have ht : (arrow b).unop ≫ v.unop = (arrow a).unop := by
    rw [← unop_comp, hv]
  have hi : Epi ((arrow b).unop ≫ v.unop) := ht ▸ inferInstance
  letI : Epi v.unop := CategoryTheory.epi_of_epi (arrow b).unop v.unop
  refine ⟨⟨Over.homMk ⟨v, (reedyOp_direct v).mpr inferInstance⟩ ?_⟩⟩
  apply WideSubcategory.hom_ext
  exact hv

/-- The constructed comparison is exactly the supplied original opposite-simplex map. -/
theorem comparison_homMk {m d : ℕ} {α : ⦋m⦌ ⟶ ⦋d⦌} {a b : Index α}
    (v : source a ⟶ source b) (hv : v ≫ arrow b = arrow a) : comparison (homMk v hv) = v := rfl

/-- Each residual factor of an original epi is itself an original simplex epi. -/
instance factor_epi {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌) [Epi α] (a : Index α) : Epi (factor α a) := by
  have hi : Epi ((arrow a).unop ≫ factor α a) := (factor_eq α a).symm ▸ inferInstance
  exact CategoryTheory.epi_of_epi (arrow a).unop (factor α a)

/-- The direct inclusion keeps every original latching object and its whole residual factor. -/
@[implicit_reducible]
def toPlus {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) (p : Fin (n + 1))
    (hp : p ∉ adjacentKernel α) : Index α ⥤ Index (plus α p hp) where
  obj a := ⟨a.obj, ⟨factor α a ≫ σ (targetIndex α p hp), by
    change (arrow a).unop ≫ (factor α a ≫ σ (targetIndex α p hp)) = plus α p hp
    rw [← Category.assoc, factor_eq]
    rfl⟩⟩
  map f := ⟨f.hom⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The direct inclusion keeps the original complete source object. -/
theorem source_toPlus {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) (p : Fin (n + 1))
    (hp : p ∉ adjacentKernel α) (a : Index α) : source ((toPlus α p hp).obj a) = source a := rfl

/-- The direct inclusion keeps the original complete epi arrow. -/
theorem arrow_toPlus {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) (p : Fin (n + 1))
    (hp : p ∉ adjacentKernel α) (a : Index α) : arrow ((toPlus α p hp).obj a) = arrow a := rfl

/-- The direct inclusion keeps every original comparison map. -/
theorem comparison_toPlus {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) (p : Fin (n + 1))
    (hp : p ∉ adjacentKernel α) {a b : Index α} (f : a ⟶ b) :
    comparison ((toPlus α p hp).map f) = comparison f := rfl

/-- The original source codegeneracy is the distinguished actual object of the new index. -/
@[implicit_reducible]
def qObject {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α]
    (p : Fin (n + 1)) (hp : p ∉ adjacentKernel α) : Index (plus α p hp) :=
  mk (plus α p hp) (σ p) (Nat.lt_succ_self n) (res α p hp) (res_square α p hp)

/-- Composition with the original source codegeneracy retains each original residual epi. -/
@[implicit_reducible]
def resToPlusObj {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α]
    (p : Fin (n + 1)) (hp : p ∉ adjacentKernel α) (a : Index (res α p hp)) :
    Index (plus α p hp) :=
  mk (plus α p hp) (σ p ≫ (arrow a).unop)
    ((source_lt a).trans (Nat.lt_succ_self n)) (factor (res α p hp) a) (by
      rw [Category.assoc, factor_eq]
      exact res_square α p hp)

/-- The residual composition retains every original comparison triangle. -/
@[implicit_reducible]
def resToPlus {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α]
    (p : Fin (n + 1)) (hp : p ∉ adjacentKernel α) :
    Index (res α p hp) ⥤ Index (plus α p hp) where
  obj a := resToPlusObj α p hp a
  map {a b} f := homMk (comparison (α := res α p hp) f) (by
    apply Quiver.Hom.unop_inj
    rw [unop_comp]
    change (σ p ≫ (arrow b).unop) ≫ (comparison f).unop = σ p ≫ (arrow a).unop
    rw [Category.assoc, ← unop_comp, comparison_arrow])
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- The original residual epi comparison into the distinguished source codegeneracy object. -/
def resToQ {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α]
    (p : Fin (n + 1)) (hp : p ∉ adjacentKernel α) (a : Index (res α p hp)) :
    (resToPlus α p hp).obj a ⟶ qObject α p hp :=
  homMk (arrow a) (by
    apply Quiver.Hom.unop_inj
    rw [unop_comp]
    rfl)

/-- The vertex lift keeps the full original residual factor as its corresponding lifted factor. -/
@[implicit_reducible]
def liftObj {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α]
    (p : Fin (n + 1)) (hp : p ∉ adjacentKernel α) (a : Index (res α p hp)) : Index α :=
  mk α (liftAt p (arrow a).unop) (Nat.succ_lt_succ (source_lt a))
    (liftAt ((arrow a).unop.toOrderHom p) (factor (res α p hp) a)) (by
      rw [liftAt_comp, factor_eq, liftAt_res])

/-- The lifted full original epi-factor functor retains each original comparison with its own pivot.
-/
@[implicit_reducible]
def liftIndex {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α]
    (p : Fin (n + 1)) (hp : p ∉ adjacentKernel α) : Index (res α p hp) ⥤ Index α where
  obj a := liftObj α p hp a
  map {a b} f := homMk (liftAt ((arrow b).unop.toOrderHom p) (comparison f).unop).op (by
    apply Quiver.Hom.unop_inj
    rw [unop_comp]
    change liftAt p (arrow b).unop ≫
      liftAt ((arrow b).unop.toOrderHom p) (comparison f).unop = liftAt p (arrow a).unop
    rw [liftAt_comp, ← unop_comp, comparison_arrow])
  map_id _ := Subsingleton.elim _ _
  map_comp _ _ := Subsingleton.elim _ _

/-- Each bridge in the actual new index is the original target codegeneracy of that residual epi. -/
def liftBridge {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α]
    (p : Fin (n + 1)) (hp : p ∉ adjacentKernel α) (a : Index (res α p hp)) :
    (resToPlus α p hp).obj a ⟶ (toPlus α p hp).obj ((liftIndex α p hp).obj a) :=
  homMk (σ ((arrow a).unop.toOrderHom p)).op (by
    apply Quiver.Hom.unop_inj
    rw [unop_comp]
    exact liftAt_square p (arrow a).unop)

/-- The complete original bridge is natural in every retained original residual comparison. -/
def bridge {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α]
    (p : Fin (n + 1)) (hp : p ∉ adjacentKernel α) :
    resToPlus α p hp ⟶ liftIndex α p hp ⋙ toPlus α p hp where
  app a := liftBridge α p hp a
  naturality _ _ _ := Subsingleton.elim _ _

end SimplexCategory.PartialLatching.Insertion

end
end
end

section



/-!
# Original mixed epi-factor comparison triangles

A comparison from a newly collapsed factor to an old noncollapsed factor
lifts through the same original epi. Both its original comparison and target
codegeneracy are recovered by the complete lifted triangle.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Simplicial

namespace SimplexCategory.EpiInsertion

/-- A mixed original comparison factors through the original lifted residual epi. -/
theorem exists_mixedComparison {n : ℕ} {B K : SimplexCategory} (p : Fin (n + 1))
    (g : ⦋n + 1⦌ ⟶ B) [Epi g] (hg : p ∉ adjacentKernel g)
    (h : ⦋n⦌ ⟶ K) (v : B ⟶ K) (hv : g ≫ v = σ p ≫ h) :
    ∃ w : B ⟶ ⦋K.len + 1⦌, g ≫ w = liftAt p h := by
  apply (exists_factor_iff_adjacentKernel_subset g (liftAt p h)).mpr
  have H : adjacentKernel g ⊆ adjacentKernel (σ p ≫ h) :=
    (exists_factor_iff_adjacentKernel_subset g (σ p ≫ h)).mp ⟨v, hv⟩
  intro i hi
  have hn : i ≠ p := by
    rintro rfl
    exact hg hi
  obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hn
  rw [← hj] at hi ⊢
  exact (mem_adjacentKernel_liftAt_shift p h j).mpr
    ((mem_adjacentKernel_sigma_shift p h j).mp (H hi))

/-- The actual mixed lifted comparison determined by its whole original epi triangle. -/
def mixedComparison {n : ℕ} {B K : SimplexCategory} (p : Fin (n + 1))
    (g : ⦋n + 1⦌ ⟶ B) [Epi g] (hg : p ∉ adjacentKernel g)
    (h : ⦋n⦌ ⟶ K) (v : B ⟶ K) (hv : g ≫ v = σ p ≫ h) : B ⟶ ⦋K.len + 1⦌ :=
  (exists_mixedComparison p g hg h v hv).choose

/-- The mixed comparison retains the exact original lifted epi factor equation. -/
theorem mixedComparison_square {n : ℕ} {B K : SimplexCategory} (p : Fin (n + 1))
    (g : ⦋n + 1⦌ ⟶ B) [Epi g] (hg : p ∉ adjacentKernel g)
    (h : ⦋n⦌ ⟶ K) (v : B ⟶ K) (hv : g ≫ v = σ p ≫ h) :
    g ≫ mixedComparison p g hg h v hv = liftAt p h :=
  (exists_mixedComparison p g hg h v hv).choose_spec

/-- The target codegeneracy of the mixed lift recovers the original whole comparison map. -/
theorem mixedComparison_target {n : ℕ} {B K : SimplexCategory} (p : Fin (n + 1))
    (g : ⦋n + 1⦌ ⟶ B) [Epi g] (hg : p ∉ adjacentKernel g)
    (h : ⦋n⦌ ⟶ K) (v : B ⟶ K) (hv : g ≫ v = σ p ≫ h) :
    mixedComparison p g hg h v hv ≫ σ (h.toOrderHom p) = v := by
  apply (cancel_epi g).mp
  rw [← Category.assoc, mixedComparison_square, liftAt_square, hv]

/-- Original epi cancellation makes the entire mixed lifted comparison unique. -/
theorem mixedComparison_unique {n : ℕ} {B K : SimplexCategory} (p : Fin (n + 1))
    (g : ⦋n + 1⦌ ⟶ B) [Epi g] (hg : p ∉ adjacentKernel g)
    (h : ⦋n⦌ ⟶ K) (v : B ⟶ K) (hv : g ≫ v = σ p ≫ h)
    (w : B ⟶ ⦋K.len + 1⦌) (hw : g ≫ w = liftAt p h) :
    w = mixedComparison p g hg h v hv :=
  (cancel_epi g).mp (hw.trans (mixedComparison_square p g hg h v hv).symm)

/-- A mixed comparison into an original proper epi forces the residual epi to remain proper. -/
theorem mixedComparison_residual_proper {n : ℕ} {B K : SimplexCategory} (p : Fin (n + 1))
    (g : ⦋n + 1⦌ ⟶ B) [Epi g] (hg : p ∉ adjacentKernel g) (hproper : B.len < n + 1)
    (h : ⦋n⦌ ⟶ K) [Epi h] (v : B ⟶ K) (hv : g ≫ v = σ p ≫ h) : K.len < n := by
  have hi : Epi (g ≫ mixedComparison p g hg h v hv) :=
    (mixedComparison_square p g hg h v hv).symm ▸ inferInstance
  let _ : Epi (mixedComparison p g hg h v hv) :=
    CategoryTheory.epi_of_epi g (mixedComparison p g hg h v hv)
  have hl : K.len + 1 ≤ B.len := len_le_of_epi (mixedComparison p g hg h v hv)
  exact Nat.lt_of_succ_lt_succ (hl.trans_lt hproper)

end SimplexCategory.EpiInsertion

end
end
end

section



/-!
# Original old and newly collapsed epi-factor objects

The original kernel criterion classifies every object of the actual new full
latching subcategory. Original comparison triangles give both residual
comparisons and the mixed lifted comparisons used to glue complete cocones.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Simplicial
open SimplexCategory.EpiInsertion

namespace SimplexCategory.PartialLatching.Insertion

/-- Every retained original proper epi collapses only pairs collapsed by the original source map. -/
theorem arrow_kernel_subset {m d : ℕ} (α : ⦋m⦌ ⟶ ⦋d⦌) (a : Index α) :
    adjacentKernel (arrow a).unop ⊆ adjacentKernel α :=
  (exists_factor_iff_adjacentKernel_subset (arrow a).unop α).mp ⟨factor α a, factor_eq α a⟩

/-- The original missing collapse is missing from every original old factor. -/
theorem old_not_collapsed {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌)
    (p : Fin (n + 1)) (hp : p ∉ adjacentKernel α) (a : Index α) :
    p ∉ adjacentKernel (arrow a).unop := fun h ↦ hp (arrow_kernel_subset α a h)

/-- Each actual noncollapsed new factor is the same original object in the old full subcategory. -/
@[implicit_reducible]
def oldObject {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α]
    (p : Fin (n + 1)) (hp : p ∉ adjacentKernel α) (a : Index (plus α p hp))
    (ha : p ∉ adjacentKernel (arrow a).unop) : Index α :=
  ⟨a.obj, (exists_factor_iff_adjacentKernel_subset (arrow a).unop α).mpr (by
    intro i hi
    have H := arrow_kernel_subset (plus α p hp) a hi
    rw [adjacentKernel_plus, Finset.mem_insert] at H
    rcases H with he | he
    · subst i
      exact (ha hi).elim
    · exact he)⟩

/-- Reinserting the old object retains that exact original new-index object. -/
theorem toPlus_oldObject {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α]
    (p : Fin (n + 1)) (hp : p ∉ adjacentKernel α) (a : Index (plus α p hp))
    (ha : p ∉ adjacentKernel (arrow a).unop) :
    (toPlus α p hp).obj (oldObject α p hp a ha) = a :=
  ObjectProperty.FullSubcategory.ext rfl

/-- Classifying an included original old factor returns the same complete original factor object. -/
theorem oldObject_toPlus {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α]
    (p : Fin (n + 1)) (hp : p ∉ adjacentKernel α) (a : Index α) :
    oldObject α p hp ((toPlus α p hp).obj a) (old_not_collapsed α p hp a) = a :=
  ObjectProperty.FullSubcategory.ext rfl

/-- Original old-to-old comparison maps are unchanged in the original old full subcategory. -/
def oldHom {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α]
    (p : Fin (n + 1)) (hp : p ∉ adjacentKernel α)
    {a b : Index (plus α p hp)} (ha : p ∉ adjacentKernel (arrow a).unop)
    (hb : p ∉ adjacentKernel (arrow b).unop) (f : a ⟶ b) :
    oldObject α p hp a ha ⟶ oldObject α p hp b hb := ⟨f.hom⟩

/-- Every actual newly collapsed original epi factors through the original source codegeneracy. -/
theorem exists_residual {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌)
    (p : Fin (n + 1)) (hp : p ∉ adjacentKernel α) (a : Index (plus α p hp))
    (ha : p ∈ adjacentKernel (arrow a).unop) :
    ∃ h : ⦋n⦌ ⟶ (source a).unop, σ p ≫ h = (arrow a).unop := by
  apply (exists_factor_iff_adjacentKernel_subset (σ p) (arrow a).unop).mpr
  rw [adjacentKernel_sigma]
  intro i hi
  have he : i = p := Finset.mem_singleton.mp hi
  subst i
  exact ha

/-- The original full residual epi of an actual newly collapsed factor. -/
def residual {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌)
    (p : Fin (n + 1)) (hp : p ∉ adjacentKernel α) (a : Index (plus α p hp))
    (ha : p ∈ adjacentKernel (arrow a).unop) : ⦋n⦌ ⟶ (source a).unop :=
  (exists_residual α p hp a ha).choose

/-- The actual newly collapsed residual retains its whole original source codegeneracy square. -/
theorem residual_square {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌)
    (p : Fin (n + 1)) (hp : p ∉ adjacentKernel α) (a : Index (plus α p hp))
    (ha : p ∈ adjacentKernel (arrow a).unop) :
    σ p ≫ residual α p hp a ha = (arrow a).unop :=
  (exists_residual α p hp a ha).choose_spec

/-- The newly collapsed residual is the original unique residual simplex map. -/
theorem residual_unique {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌)
    (p : Fin (n + 1)) (hp : p ∉ adjacentKernel α) (a : Index (plus α p hp))
    (ha : p ∈ adjacentKernel (arrow a).unop) (h : ⦋n⦌ ⟶ (source a).unop)
    (hh : σ p ≫ h = (arrow a).unop) : h = residual α p hp a ha :=
  (cancel_epi (σ p)).mp (hh.trans (residual_square α p hp a ha).symm)

/-- The actual new-factor residual remains an original simplex epimorphism. -/
instance residual_epi {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌)
    (p : Fin (n + 1)) (hp : p ∉ adjacentKernel α) (a : Index (plus α p hp))
    (ha : p ∈ adjacentKernel (arrow a).unop) : Epi (residual α p hp a ha) := by
  have hi : Epi (σ p ≫ residual α p hp a ha) :=
    (residual_square α p hp a ha).symm ▸ inferInstance
  exact CategoryTheory.epi_of_epi (σ p) (residual α p hp a ha)

/-- Each complete original residual factor descends to the complete original lower target map. -/
theorem residual_factor {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α]
    (p : Fin (n + 1)) (hp : p ∉ adjacentKernel α) (a : Index (plus α p hp))
    (ha : p ∈ adjacentKernel (arrow a).unop) :
    residual α p hp a ha ≫ factor (plus α p hp) a = res α p hp := by
  apply (cancel_epi (σ p)).mp
  rw [← Category.assoc, residual_square, factor_eq, res_square]
  rfl

/-- Every newly collapsed original object has its original residual comparison into the σp object.
-/
def residualToQ {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α]
    (p : Fin (n + 1)) (hp : p ∉ adjacentKernel α) (a : Index (plus α p hp))
    (ha : p ∈ adjacentKernel (arrow a).unop) : a ⟶ qObject α p hp :=
  homMk (residual α p hp a ha).op (by
    apply Quiver.Hom.unop_inj
    rw [unop_comp]
    exact residual_square α p hp a ha)

/-- The original source codegeneracy object has the actual newly collapsed pivot. -/
theorem qObject_collapsed {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α]
    (p : Fin (n + 1)) (hp : p ∉ adjacentKernel α) :
    p ∈ adjacentKernel (arrow (qObject α p hp)).unop := by
  change p ∈ adjacentKernel (σ p)
  rw [adjacentKernel_sigma]
  exact Finset.mem_singleton_self p

/-- The distinguished source codegeneracy has the exact original identity as its residual. -/
theorem residual_qObject {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α]
    (p : Fin (n + 1)) (hp : p ∉ adjacentKernel α)
    (ha : p ∈ adjacentKernel (arrow (qObject α p hp)).unop) :
    residual α p hp (qObject α p hp) ha = 𝟙 ⦋n⦌ := by
  apply (cancel_epi (σ p)).mp
  rw [residual_square, Category.comp_id]
  rfl

/-- Every original retained comparison carries whole adjacent-kernel inclusion. -/
theorem comparison_kernel_subset {m d : ℕ} {α : ⦋m⦌ ⟶ ⦋d⦌} {a b : Index α}
    (f : a ⟶ b) : adjacentKernel (arrow b).unop ⊆ adjacentKernel (arrow a).unop :=
  (exists_factor_iff_adjacentKernel_subset (arrow b).unop (arrow a).unop).mp
    ⟨(comparison f).unop, by rw [← unop_comp, comparison_arrow]⟩

/-- Newly collapsed-to-newly collapsed comparisons retain the whole original residual triangle. -/
theorem residual_comparison {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌)
    (p : Fin (n + 1)) (hp : p ∉ adjacentKernel α)
    {a b : Index (plus α p hp)} (ha : p ∈ adjacentKernel (arrow a).unop)
    (hb : p ∈ adjacentKernel (arrow b).unop) (f : a ⟶ b) :
    residual α p hp b hb ≫ (comparison f).unop = residual α p hp a ha := by
  apply (cancel_epi (σ p)).mp
  rw [← Category.assoc, residual_square, ← unop_comp, comparison_arrow, residual_square]

/-- Every mixed original triangle has the unchanged original newly collapsed residual as its target.
-/
theorem mixed_equation {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌)
    (p : Fin (n + 1)) (hp : p ∉ adjacentKernel α)
    {a b : Index (plus α p hp)} (ha : p ∈ adjacentKernel (arrow a).unop) (f : a ⟶ b) :
    (arrow b).unop ≫ (comparison f).unop = σ p ≫ residual α p hp a ha := by
  rw [← unop_comp, comparison_arrow, residual_square]

/-- A mixed original triangle gives an actual original proper factor of the lower residual map. -/
@[implicit_reducible]
def mixedResidualObject {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α]
    (p : Fin (n + 1)) (hp : p ∉ adjacentKernel α)
    {a b : Index (plus α p hp)} (ha : p ∈ adjacentKernel (arrow a).unop)
    (hb : p ∉ adjacentKernel (arrow b).unop) (f : a ⟶ b) : Index (res α p hp) :=
  mk (res α p hp) (residual α p hp a ha)
    (mixedComparison_residual_proper p (arrow b).unop hb (source_lt b)
      (residual α p hp a ha) (comparison f).unop (mixed_equation α p hp ha f))
    (factor (plus α p hp) a) (residual_factor α p hp a ha)

/-- The mixed original comparison lifts from that same actual lower factor to the old object. -/
def mixedLiftToOld {n d : ℕ} (α : ⦋n + 1⦌ ⟶ ⦋d + 1⦌) [Epi α]
    (p : Fin (n + 1)) (hp : p ∉ adjacentKernel α)
    {a b : Index (plus α p hp)} (ha : p ∈ adjacentKernel (arrow a).unop)
    (hb : p ∉ adjacentKernel (arrow b).unop) (f : a ⟶ b) :
    (liftIndex α p hp).obj (mixedResidualObject α p hp ha hb f) ⟶ oldObject α p hp b hb :=
  homMk (mixedComparison p (arrow b).unop hb (residual α p hp a ha)
    (comparison f).unop (mixed_equation α p hp ha f)).op (by
    apply Quiver.Hom.unop_inj
    rw [unop_comp]
    exact mixedComparison_square p (arrow b).unop hb (residual α p hp a ha)
      (comparison f).unop (mixed_equation α p hp ha f))

end SimplexCategory.PartialLatching.Insertion

end
end
end

section



/-!
# A genuine epi with positive target has an uncollapsed adjacent pair

The proof uses the original simplex epi factorization through the original collapse to
`[0]`. Thus the existence needed by partial-boundary induction follows from the original
epi and does not require a kernel-cardinality or class-preservation premise.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open CategoryTheory Simplicial

namespace SimplexCategory

/-- Every original epi to a positive-degree simplex retains an adjacent pair. -/
theorem exists_not_mem_adjacentKernel_of_epi_positive {m d : ℕ}
    (α : ⦋m⦌ ⟶ ⦋d + 1⦌) [Epi α] : ∃ p : Fin m, p ∉ adjacentKernel α := by
  by_contra h
  have hall : ∀ p : Fin m, p ∈ adjacentKernel α := by
    simpa only [not_exists, not_not] using h
  let g : ⦋m⦌ ⟶ ⦋0⦌ := const _ _ 0
  let _ : Epi g := epi_iff_surjective.mpr (by
    intro x
    refine ⟨0, ?_⟩
    change (0 : Fin 1) = x
    exact Subsingleton.elim _ _)
  obtain ⟨β, hβ⟩ := (exists_factor_iff_adjacentKernel_subset g α).mpr
    (fun p _ => hall p)
  let _ : Epi (g ≫ β) := by rw [hβ]; infer_instance
  let _ : Epi β := epi_of_epi g β
  have hlen : d + 1 ≤ 0 := len_le_of_epi β
  exact Nat.not_succ_le_zero d hlen

end SimplexCategory

end
end
end
