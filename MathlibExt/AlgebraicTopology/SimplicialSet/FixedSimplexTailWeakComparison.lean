/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.FixedSimplexTailColimitGeometry
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.RealizationWeakEquivalenceSequentialMono

/-!
# Weak fixed-base comparisons from finite sequence tails

For a sequence map with monic source transitions, sharp components on a chosen tail, and weak incoming comparisons from its starting stage to every later stage, the canonical map from the starting pullback to the corresponding pullback of colimits is a weak equivalence. This map is natural in the fixed base map, and base changes by weak equivalences induce weak maps between the resulting colimit pullbacks.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace SSet.RezkFixedSimplexTail
open RezkTailPullbackColimit SharpComparisonDraft

/-- The actual finite-to-total point-fibre map into the nested final cocone. -/
def toNestedTotal {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y) (n : ℕ)
    {T : SSet.{u}} (b : T ⟶ Y.obj n)
    (cX : Cocone X) (cY : Cocone Y) (q : cX.pt ⟶ cY.pt)
    (hq : ∀ m, cX.ι.app m ≫ q = p.app m ≫ cY.ι.app m) :
    pullback (p.app n) b ⟶ (cocone p n b cX cY q hq).pt := by
  change pullback (p.app n) b ⟶ pullback (pullback.snd q (cY.ι.app n)) b
  exact pullback.lift
    (pullback.lift (pullback.fst (p.app n) b ≫ cX.ι.app n)
      (pullback.snd (p.app n) b ≫ b) (by
        calc
          (pullback.fst (p.app n) b ≫ cX.ι.app n) ≫ q =
              pullback.fst (p.app n) b ≫ (p.app n ≫ cY.ι.app n) := by
            rw [Category.assoc, hq n]
          _ = (pullback.snd (p.app n) b ≫ b) ≫ cY.ι.app n := by
            rw [← Category.assoc, pullback.condition]))
    (pullback.snd (p.app n) b) (by simp only [pullback.lift_snd])

/-- Every component commutes with BOTH actual colimit cocone projections. -/
theorem component_total_naturality {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y) (n : ℕ)
    {T : SSet.{u}} (b : T ⟶ Y.obj n)
    (cX : Cocone X) (cY : Cocone Y) (q : cX.pt ⟶ cY.pt)
    (hq : ∀ m, cX.ι.app m ≫ q = p.app m ≫ cY.ι.app m) (k : ℕ) :
    component p n b k ≫ (cocone p n b cX cY q hq).ι.app k =
      toNestedTotal p n b cX cY q hq := by
  let u : pullback (p.app n) b ⟶
      pullback (p.app (n + k)) (Y.map (homOfLE (Nat.le_add_right n k))) :=
    pullback.lift (pullback.fst (p.app n) b ≫ X.map (homOfLE (Nat.le_add_right n k)))
      (pullback.snd (p.app n) b ≫ b) (by
        rw [Category.assoc, p.naturality, ← Category.assoc, pullback.condition, Category.assoc])
  let v : pullback (p.app (n + k)) (Y.map (homOfLE (Nat.le_add_right n k))) ⟶
      pullback q (cY.ι.app n) := (tailPullbackCocone p n cX cY q hq).ι.app k
  let w : pullback (p.app n) b ⟶ pullback q (cY.ι.app n) :=
    pullback.lift (pullback.fst (p.app n) b ≫ cX.ι.app n)
      (pullback.snd (p.app n) b ≫ b) (by
        rw [Category.assoc, hq n, ← Category.assoc, pullback.condition, Category.assoc])
  have hvfst : v ≫ pullback.fst q (cY.ι.app n) =
      pullback.fst (p.app (n + k)) (Y.map (homOfLE (Nat.le_add_right n k))) ≫
        cX.ι.app (n + k) := (tailPullbackCocone_legs p n cX cY q hq k).1
  have hvsnd : v ≫ pullback.snd q (cY.ι.app n) =
      pullback.snd (p.app (n + k)) (Y.map (homOfLE (Nat.le_add_right n k))) :=
    (tailPullbackCocone_legs p n cX cY q hq k).2
  have huv : u ≫ v = w := by
    apply pullback.hom_ext
    · rw [Category.assoc, hvfst]
      simp [u, w, Category.assoc, cX.ι.naturality (homOfLE (Nat.le_add_right n k))]
    · rw [Category.assoc, hvsnd]
      simp [u, w]
  change pullback.lift
      (f := pullback.snd (p.app (n + k)) (Y.map (homOfLE (Nat.le_add_right n k))))
      (g := b) u (pullback.snd (p.app n) b)
      (by simp only [u, pullback.lift_snd]) ≫
    pullback.lift (f := pullback.snd q (cY.ι.app n)) (g := b)
      (pullback.fst (pullback.snd (p.app (n + k))
        (Y.map (homOfLE (Nat.le_add_right n k)))) b ≫ v)
      (pullback.snd (pullback.snd (p.app (n + k))
        (Y.map (homOfLE (Nat.le_add_right n k)))) b)
      (by rw [Category.assoc, hvsnd, pullback.condition]) =
    pullback.lift (f := pullback.snd q (cY.ι.app n)) (g := b)
      w (pullback.snd (p.app n) b) (by simp only [w, pullback.lift_snd])
  apply pullback.hom_ext
  · simpa only [Category.assoc, pullback.lift_fst_assoc, pullback.lift_fst] using huv
  · simp only [Category.assoc, pullback.lift_snd]

/-- The real finite-to-total fibre map is weak by native sequential Mono,
with all component WEs DERIVED from finite Sharp and incoming HC. -/
theorem to_total_weak
    {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y) (n : ℕ)
    {T : SSet.{u}} (b : T ⟶ Y.obj n)
    (cX : Cocone X) (cY : Cocone Y) (q : cX.pt ⟶ cY.pt)
    (hq : ∀ m, cX.ι.app m ≫ q = p.app m ≫ cY.ι.app m)
    (hX : IsColimit cX) (hY : IsColimit cY)
    (hmX : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), Mono (X.map f))
    (hsharp : ∀ k, Sharp (p.app (n + k)))
    (hincoming : ∀ k, WeakEquivalence
      (pullback.lift (X.map (homOfLE (Nat.le_add_right n k))) (p.app n)
        (p.naturality (homOfLE (Nat.le_add_right n k))) ≫
        comparison (p.app (n + k)) (Y.map (homOfLE (Nat.le_add_right n k))))) :
    WeakEquivalence (toNestedTotal p n b cX cY q hq ≫ (finalIso p n b cX cY q hq).hom) := by
  have hcomponents (k : ℕ) : realizationWeakEquivalences ((constantComparison p n b).app k) := by
    exact (HomotopicalAlgebra.weakEquivalence_iff _).1
      (component_weak p n b k (by simpa using hsharp 0) (hsharp k) (hincoming k))
  let : IsConnected ℕ := CategoryTheory.IsFiltered.isConnected ℕ
  have weakNested : realizationWeakEquivalences (toNestedTotal p n b cX cY q hq) :=
    realizationWeakEquivalences.of_isColimit_nat_mono (constantComparison p n b)
      (isColimitConstCocone ℕ (pullback (p.app n) b))
      (coconeIsColimit p n b cX cY q hq hX hY)
      (toNestedTotal p n b cX cY q hq)
      (fun k => (component_total_naturality p n b cX cY q hq k).symm)
      (fun {i j} f => by change Mono (𝟙 (pullback (p.app n) b)); infer_instance)
      (fun {i j} f => family_map_mono p n b hmX f) hcomponents
  let : WeakEquivalence (toNestedTotal p n b cX cY q hq) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).2 weakNested
  infer_instance

/-- The same finite-to-total map with its final TWO original pullback projections. -/
def toTotal {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y) (n : ℕ)
    {T : SSet.{u}} (b : T ⟶ Y.obj n)
    (cX : Cocone X) (cY : Cocone Y) (q : cX.pt ⟶ cY.pt)
    (hq : ∀ m, cX.ι.app m ≫ q = p.app m ≫ cY.ι.app m) :
    pullback (p.app n) b ⟶ pullback q (b ≫ cY.ι.app n) :=
  pullback.lift (pullback.fst (p.app n) b ≫ cX.ι.app n)
    (pullback.snd (p.app n) b) (by
      calc
        (pullback.fst (p.app n) b ≫ cX.ι.app n) ≫ q =
            pullback.fst (p.app n) b ≫ (p.app n ≫ cY.ι.app n) := by
          rw [Category.assoc, hq n]
        _ = pullback.snd (p.app n) b ≫ (b ≫ cY.ι.app n) := by
          rw [← Category.assoc, pullback.condition, Category.assoc])

theorem toTotal_eq_nested {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y) (n : ℕ)
    {T : SSet.{u}} (b : T ⟶ Y.obj n)
    (cX : Cocone X) (cY : Cocone Y) (q : cX.pt ⟶ cY.pt)
    (hq : ∀ m, cX.ι.app m ≫ q = p.app m ≫ cY.ι.app m) :
    toTotal p n b cX cY q hq =
      toNestedTotal p n b cX cY q hq ≫ (finalIso p n b cX cY q hq).hom := by
  let e : pullback (pullback.snd q (cY.ι.app n)) b ≅
      pullback q (b ≫ cY.ι.app n) := finalIso p n b cX cY q hq
  let w : pullback (p.app n) b ⟶ pullback (pullback.snd q (cY.ι.app n)) b :=
    toNestedTotal p n b cX cY q hq
  have he1 : e.hom ≫ pullback.fst q (b ≫ cY.ι.app n) =
      pullback.fst (pullback.snd q (cY.ι.app n)) b ≫ pullback.fst q (cY.ι.app n) :=
    (SharpPullbackClosure.nestedPullbackIso_hom_legs q (cY.ι.app n) b).1
  have he2 : e.hom ≫ pullback.snd q (b ≫ cY.ι.app n) =
      pullback.snd (pullback.snd q (cY.ι.app n)) b :=
    (SharpPullbackClosure.nestedPullbackIso_hom_legs q (cY.ι.app n) b).2
  change toTotal p n b cX cY q hq = w ≫ e.hom
  apply pullback.hom_ext
  · rw [Category.assoc, he1]
    simp [id, toTotal, w, toNestedTotal]
  · rw [Category.assoc, he2]
    simp [id, toTotal, w, toNestedTotal]

/-- Naturality under the SAME operator into the originally chosen finite simplex. -/
theorem toTotal_naturality {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y) (n : ℕ)
    {S T : SSet.{u}} (w : S ⟶ T) (b : T ⟶ Y.obj n)
    (cX : Cocone X) (cY : Cocone Y) (q : cX.pt ⟶ cY.pt)
    (hq : ∀ m, cX.ι.app m ≫ q = p.app m ≫ cY.ι.app m) :
    pullback.map (p.app n) (w ≫ b) (p.app n) b (𝟙 _) w (𝟙 _) (by simp) (by simp) ≫
        toTotal p n b cX cY q hq =
      toTotal p n (w ≫ b) cX cY q hq ≫
        pullback.map q ((w ≫ b) ≫ cY.ι.app n) q (b ≫ cY.ι.app n)
          (𝟙 _) w (𝟙 _) (by simp) (by simp [Category.assoc]) := by
  apply pullback.hom_ext <;> simp [toTotal, pullback.map, Category.assoc]

/-- Two actual finite-to-total WEs and finite Sharp give the original total
operator comparison weak. No total Sharp is assumed or used. -/
theorem total_operator_weak
    {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y) (n : ℕ)
    {S T : SSet.{u}} (w : S ⟶ T) (b : T ⟶ Y.obj n)
    (cX : Cocone X) (cY : Cocone Y) (q : cX.pt ⟶ cY.pt)
    (hq : ∀ m, cX.ι.app m ≫ q = p.app m ≫ cY.ι.app m)
    (hX : IsColimit cX) (hY : IsColimit cY)
    (hmX : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), Mono (X.map f))
    (hsharp : ∀ k, Sharp (p.app (n + k)))
    (hincoming : ∀ k, WeakEquivalence
      (pullback.lift (X.map (homOfLE (Nat.le_add_right n k))) (p.app n)
        (p.naturality (homOfLE (Nat.le_add_right n k))) ≫
        comparison (p.app (n + k)) (Y.map (homOfLE (Nat.le_add_right n k)))))
    (hw : WeakEquivalence w) :
    WeakEquivalence
      (pullback.map q ((w ≫ b) ≫ cY.ι.app n) q (b ≫ cY.ι.app n)
        (𝟙 _) w (𝟙 _) (by simp) (by simp [Category.assoc])) := by
  have hp0 : Sharp (p.app n) := by simpa using hsharp 0
  have finiteWeak := SharpComparisonDraft.Sharp.baseChange (p.app n) hp0 S T w b hw
  have totalB : WeakEquivalence (toTotal p n b cX cY q hq) := by
    rw [toTotal_eq_nested]
    exact to_total_weak p n b cX cY q hq hX hY hmX hsharp hincoming
  have totalWB : WeakEquivalence (toTotal p n (w ≫ b) cX cY q hq) := by
    rw [toTotal_eq_nested]
    exact to_total_weak p n (w ≫ b) cX cY q hq hX hY hmX hsharp hincoming
  let := finiteWeak
  let := totalB
  let := totalWB
  have comp : WeakEquivalence
      (pullback.map (p.app n) (w ≫ b) (p.app n) b (𝟙 _) w (𝟙 _) (by simp) (by simp) ≫
        toTotal p n b cX cY q hq) := by infer_instance
  rw [toTotal_naturality] at comp
  let := comp
  exact weakEquivalence_of_precomp (toTotal p n (w ≫ b) cX cY q hq) _

end SSet.RezkFixedSimplexTail
