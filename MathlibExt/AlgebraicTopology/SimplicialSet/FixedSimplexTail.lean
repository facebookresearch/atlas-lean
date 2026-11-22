/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.TailPullbackTransitionMono
import MathlibExt.AlgebraicTopology.SimplicialSet.SharpPullbackClosure
import MathlibExt.AlgebraicTopology.SimplicialSet.CompatiblePushoutHCTransport
import MathlibExt.AlgebraicTopology.SimplicialSet.OverPullbackFilteredColimits
import Mathlib.CategoryTheory.Limits.Over
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-!
# Pullback tail diagrams at a fixed simplex

The actual fixed-simplex tail, with constant source PB(p_n,b).

No final sharpness or basechanged weak map is supplied. Each component's
weakness is derived from the finite incoming HC comparison and the actual
two finite sharp arrows before any total-map claim.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped SSet.modelCategoryQuillen

namespace SSet.RezkFixedSimplexTail
open RezkTailPullbackColimit SharpComparisonDraft RezkCompatiblePushout

/-- The original tail pullbacks, all over the same finite base Y_n. -/
def tailOver {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y) (n : ℕ) : ℕ ⥤ Over (Y.obj n) where
  obj k := Over.mk (pullback.snd (p.app (n + k)) (Y.map (homOfLE (Nat.le_add_right n k))))
  map f := Over.homMk ((tailPullbackDiagram p n).map f) (tailPullbackDiagram_map_legs p n f).2
  map_id k := by
    apply Over.OverMorphism.ext
    change (tailPullbackDiagram p n).map (𝟙 k) = 𝟙 _
    exact (tailPullbackDiagram p n).map_id k
  map_comp f g := by
    apply Over.OverMorphism.ext
    change (tailPullbackDiagram p n).map (f ≫ g) =
      (tailPullbackDiagram p n).map f ≫ (tailPullbackDiagram p n).map g
    exact (tailPullbackDiagram p n).map_comp f g

/-- Pull the original tail back AFTER choosing this particular original finite simplex. -/
def family {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y) (n : ℕ)
    {T : SSet.{u}} (b : T ⟶ Y.obj n) : ℕ ⥤ SSet.{u} :=
  tailOver p n ⋙ Over.pullback b ⋙ Over.forget T

/-- The actual component, before flattening: the source is PB(p_n,b), never X_n. -/
def component {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y) (n : ℕ)
    {T : SSet.{u}} (b : T ⟶ Y.obj n) (k : ℕ) :
    pullback (p.app n) b ⟶ (family p n b).obj k := by
  change pullback (p.app n) b ⟶
    pullback (pullback.snd (p.app (n + k)) (Y.map (homOfLE (Nat.le_add_right n k)))) b
  exact pullback.lift
    (pullback.lift
      (pullback.fst (p.app n) b ≫ X.map (homOfLE (Nat.le_add_right n k)))
      (pullback.snd (p.app n) b ≫ b) (by
        calc
          (pullback.fst (p.app n) b ≫ X.map (homOfLE (Nat.le_add_right n k))) ≫ p.app (n + k) =
              pullback.fst (p.app n) b ≫ (p.app n ≫ Y.map (homOfLE (Nat.le_add_right n k))) := by
            rw [Category.assoc, ← p.naturality]
          _ = (pullback.snd (p.app n) b ≫ b) ≫ Y.map (homOfLE (Nat.le_add_right n k)) := by
            rw [← Category.assoc, pullback.condition]))
    (pullback.snd (p.app n) b) (by simp only [pullback.lift_snd])

/-- Actual constant-to-tail naturality, with both projections and the original transition. -/
def constantComparison {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y) (n : ℕ)
    {T : SSet.{u}} (b : T ⟶ Y.obj n) :
    (Functor.const ℕ).obj (pullback (p.app n) b) ⟶ family p n b where
  app k := component p n b k
  naturality := by
    intro i j f
    have hpath : homOfLE (Nat.le_add_right n i) ≫ (natTail n).map f =
        homOfLE (Nat.le_add_right n j) := Subsingleton.elim _ _
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp [component, family, tailOver, Over.pullback, Category.assoc,
          ← X.map_comp, hpath]
      · simp [component, family, tailOver, Over.pullback, Category.assoc]
    · simp [component, family, tailOver, Over.pullback, Category.assoc]

/-- The two actual flattening projections identify each nested fibre with PB(p_(n+k),b≫Y(n→n+k)). -/
def flatten {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y) (n : ℕ)
    {T : SSet.{u}} (b : T ⟶ Y.obj n) (k : ℕ) :
    (family p n b).obj k ≅
      pullback (p.app (n + k)) (b ≫ Y.map (homOfLE (Nat.le_add_right n k))) :=
  SharpPullbackClosure.nestedPullbackIso (p.app (n + k))
    (Y.map (homOfLE (Nat.le_add_right n k))) b

/-- Weakness is DERIVED by basechanging the original finite weak comparison
between p_n and the finite sharp pullback projection; p_infinity is absent. -/
theorem component_weak
    {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y) (n : ℕ)
    {T : SSet.{u}} (b : T ⟶ Y.obj n) (k : ℕ)
    (hp0 : Sharp (p.app n)) (hpk : Sharp (p.app (n + k)))
    (hc : WeakEquivalence
      (pullback.lift (X.map (homOfLE (Nat.le_add_right n k))) (p.app n)
        (p.naturality (homOfLE (Nat.le_add_right n k))) ≫
        comparison (p.app (n + k)) (Y.map (homOfLE (Nat.le_add_right n k))))) :
    WeakEquivalence (component p n b k) := by
  let y := Y.map (homOfLE (Nat.le_add_right n k))
  let c := pullback.lift (X.map (homOfLE (Nat.le_add_right n k))) (p.app n)
    (p.naturality (homOfLE (Nat.le_add_right n k)))
  let q := pullback.snd (p.app (n + k)) y
  have hcq : c ≫ q = p.app n := pullback.lift_snd _ _ _
  have wc : WeakEquivalence c := (hc_iff_ordinaryLift_weak
    (CommSq.mk (p.naturality (homOfLE (Nat.le_add_right n k)))) hpk).mp hc
  have hq : Sharp q := SharpPullbackClosure.sharp_pullback_snd (p.app (n + k)) y hpk
  have hcp : Sharp (c ≫ q) := by rw [hcq]; exact hp0
  let e : pullback (c ≫ q) b ≅ pullback (p.app n) b := pullback.congrHom hcq rfl
  have weakBasechange : WeakEquivalence (ordinaryMap c q b) := ordinaryMap_weak c q b wc hq hcp
  have factor : component p n b k = e.inv ≫ ordinaryMap c q b := by
    apply pullback.hom_ext
    · apply pullback.hom_ext <;>
        simp [component, family, tailOver, Over.pullback, e, ordinaryMap, c,
            q, y, Category.assoc, pullback.condition]
    · simp [component, family, tailOver, Over.pullback, e, ordinaryMap, c,
        q, y, Category.assoc]
  rw [factor]
  let : IsIso e.inv := e.isIso_inv
  exact (HomotopicalAlgebra.weakEquivalence_iff _).2
    (realizationWeakEquivalences.comp_mem e.inv (ordinaryMap c q b)
      (realizationWeakEquivalences.of_isIso e.inv)
      ((HomotopicalAlgebra.weakEquivalence_iff _).1 weakBasechange))

/-- The actual tail pullback family has Mono transitions from X only. -/
theorem family_map_mono
    {X Y : ℕ ⥤ SSet.{u}} (p : X ⟶ Y) (n : ℕ)
    {T : SSet.{u}} (b : T ⟶ Y.obj n)
    (hmX : ∀ ⦃i j : ℕ⦄ (f : i ⟶ j), Mono (X.map f))
    {i j : ℕ} (f : i ⟶ j) : Mono ((family p n b).map f) := by
  let : Mono ((tailOver p n).map f) := by
    let : Mono (((tailOver p n).map f).left) := by
      change Mono ((tailPullbackDiagram p n).map f)
      exact tailPullbackDiagram_map_mono p n hmX f
    exact Over.mono_of_mono_left ((tailOver p n).map f)
  let : Mono ((Over.pullback b).map ((tailOver p n).map f)) :=
    preserves_mono_of_preservesLimit (Over.pullback b) ((tailOver p n).map f)
  change Mono (((Over.pullback b).map ((tailOver p n).map f)).left)
  exact Over.mono_left_of_mono _

end SSet.RezkFixedSimplexTail
