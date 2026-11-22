/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeWordShapeSpaces
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.SimplicialModel

/-!
# Actual finite word-shape attaching boundaries

The boundary is the union where one actual target letter is in the given
attaching image. Every original Hom-segment factor remains unrestricted.
Native scalar union-product corners prove the positive shape inclusions
anodyne for actual anodyne attaching maps. The zero-letter boundary is
empty, and no weak assertion is made for its original old Hom stage.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
open RelativeWords

variable {O : Type u} {C : FixedObjects O}

/-- The actual shape boundary in which at least one supplied target letter is an attaching image. -/
def shapeBoundary (T : Data C) : {n : ℕ} → (s : Shape O n) → (a b : O) →
    (shapeSpace T s a b).Subcomplex
  | 0, .nil, _a, _b => ⊥
  | _n + 1, .cons x y s, a, b =>
      (⊥ : (hom C a x).Subcomplex).unionProd
        ((SSet.Subcomplex.range (T.inclusion x y)).unionProd (shapeBoundary T s y b))

/-- Actual decoded shape words have new-letter count at most the supplied finite shape length. -/
theorem countAt_shapeDecode_le (T : Data C) (q : SimplexCategoryᵒᵖ) {n : ℕ} (s : Shape O n)
    {a b : O} (p : (shapeSpace T s a b).obj q) : countAt T q (shapeDecode T q s p) ≤ n := by
  have h := @RelativeGenerators.count_le_length O (scalarCategory C q)
    (fun x y => (T.domain.Hom x y).obj q) (fun x y => (T.target.Hom x y).obj q)
    (fun {_ _} a => inclusionAt T q a) a b (shapeDecode T q s p)
  simpa only [length_shapeDecode] using h

/-- The genuine image-union boundary is precisely the original raw-word count boundary. -/
theorem mem_shapeBoundary_iff (T : Data C) (q : SimplexCategoryᵒᵖ) {n : ℕ} (s : Shape O n)
    {a b : O} (p : (shapeSpace T s a b).obj q) :
    p ∈ (shapeBoundary T s a b).obj q ↔ countAt T q (shapeDecode T q s p) < n := by
  classical
  induction s generalizing a b with
  | nil =>
      change False ↔ 0 < 0
      simp
  | @cons n x y s ih =>
      rcases p with ⟨h, g, p⟩
      change ((True ∧ ((True ∧ p ∈ (shapeBoundary T s y b).obj q) ∨
        (g ∈ Set.range (@inclusionAt O C T q x y) ∧ True))) ∨ (False ∧ True)) ↔ _
      simp only [true_and, and_true, or_false]
      rw [ih]
      change (countAt T q (shapeDecode T q s p) < n ∨ g ∈ Set.range (@inclusionAt O C T q x y)) ↔
        @RelativeGenerators.cost O
          (fun x y => (T.domain.Hom x y).obj q) (fun x y => (T.target.Hom x y).obj q)
          (fun {_ _} a => inclusionAt T q a) x y g + countAt T q (shapeDecode T q s p) < n + 1
      have ht := countAt_shapeDecode_le T q s p
      by_cases hg : g ∈ Set.range (@inclusionAt O C T q x y)
      · have hc : @RelativeGenerators.cost O
            (fun x y => (T.domain.Hom x y).obj q) (fun x y => (T.target.Hom x y).obj q)
            (fun {_ _} a => inclusionAt T q a) x y g = 0 := by
          rw [RelativeGenerators.cost, ite_eq_left hg]
        rw [hc]
        simp only [hg, or_true, Nat.zero_add]
        exact ⟨fun _ => Nat.lt_succ_of_le ht, fun _ => True.intro⟩
      · have hc : @RelativeGenerators.cost O
            (fun x y => (T.domain.Hom x y).obj q) (fun x y => (T.target.Hom x y).obj q)
            (fun {_ _} a => inclusionAt T q a) x y g = 1 := by
          rw [RelativeGenerators.cost, ite_eq_right hg]
        rw [hc]
        simp only [hg, or_false]
        omega

/-- The attaching-image inclusion is anodyne by the actual original scalar range factorization. -/
theorem attachingRange_anodyne (T : Data C) (x y : O)
    (h : SSet.anodyneExtensions (T.inclusion x y)) :
    SSet.anodyneExtensions (SSet.Subcomplex.range (T.inclusion x y)).ι := by
  let _ : Mono (T.inclusion x y) := T.mono x y
  let e : Arrow.mk (T.inclusion x y) ≅ Arrow.mk (SSet.Subcomplex.range (T.inclusion x y)).ι :=
    Arrow.isoMk' _ _ (asIso (SSet.Subcomplex.toRange (T.inclusion x y)))
      (Iso.refl _) (SSet.Subcomplex.toRange_ι (T.inclusion x y))
  exact (SSet.anodyneExtensions.arrow_mk_iso_iff e).mp h

/-- Every positive actual shape boundary inclusion is anodyne for the supplied anodyne generators. -/
theorem shapeBoundary_anodyne (T : Data C)
    (hi : ∀ x y, SSet.anodyneExtensions (T.inclusion x y))
    {n : ℕ} (s : Shape O (n + 1)) (a b : O) : SSet.anodyneExtensions (shapeBoundary T s a b).ι := by
  cases s with
  | cons x y s =>
      exact SSet.anodyneExtensions_unionProd_ι _ _
        (SSet.anodyneExtensions_unionProd_ι' _ _ (attachingRange_anodyne T x y (hi x y)))

/-- The same actual positive shape boundary is a trivial cofibration in the native scalar model. -/
theorem shapeBoundary_trivialCofibration (T : Data C)
    (hi : ∀ x y, trivialCofibrations SSet.{u} (T.inclusion x y))
    {n : ℕ} (s : Shape O (n + 1)) (a b : O) :
    trivialCofibrations SSet.{u} (shapeBoundary T s a b).ι := by
  rw [← SSet.anodyneExtensions_eq_trivialCofibrations]
  apply shapeBoundary_anodyne T _ s a b
  intro x y
  rw [SSet.anodyneExtensions_eq_trivialCofibrations]
  exact hi x y

end CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
