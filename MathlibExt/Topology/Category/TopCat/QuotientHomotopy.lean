/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Homotopy.TopCat.Basic

/-!
# Quotient homotopies in `TopCat`

For a quotient map `q : X ⟶ Y` and a homotopy `H : I × X → Z` that factors
through `q` at each parameter `t : I`, this file descends `H` to a homotopy
`TopCat.Homotopy f g` on the quotient `Y`.

The key continuity argument uses `Topology.IsQuotientMap.continuous_lift_prod_right`:
because the parameter `unitInterval` is compact (hence locally compact), the product
`I × X → I × Y` induced by `id × q` is again a quotient map. The pointwise lifts
`s t : Y → Z` obtained from `IsQuotientMap.lift` therefore assemble to a jointly
continuous map `I × Y → Z` that agrees with `H` after precomposing with `q`.
Endpoints are checked by surjectivity of `q`.
-/

@[expose] public section

open CategoryTheory Topology TopCat
open scoped unitInterval

universe u

namespace TopCat.Homotopy

/-- Descend a continuously parameterized homotopy through a quotient map.

Given a quotient map `q : X ⟶ Y` and a continuous homotopy `H : I × X → Z`
that at each `t` factors through `q`, produce the descended homotopy
`I × Y → Z` between `f` and `g`. The hypothesis `hFactors` supplies the
factorisation at each fixed `t`; continuity of the descended homotopy in both
variables follows from `IsQuotientMap.continuous_lift_prod_right` because
`unitInterval` is locally compact. -/
noncomputable def ofQuotientMap
    {X Y Z : TopCat.{u}} (q : X ⟶ Y) (hq : IsQuotientMap q.hom)
    {f g : Y ⟶ Z} (H : C(unitInterval × X, Z))
    (h0 : ∀ x, H (0, x) = f.hom (q.hom x))
    (h1 : ∀ x, H (1, x) = g.hom (q.hom x))
    (hFactors : ∀ t : unitInterval,
      Function.FactorsThrough (fun x => H (t, x)) q.hom) :
    TopCat.Homotopy f g := by
  let Ht : unitInterval → C(X, Z) := fun t =>
    { toFun := fun x => H (t, x)
      continuous_toFun := H.continuous.comp
        (continuous_const.prodMk continuous_id) }
  refine
    { toFun := fun p => hq.lift (Ht p.1) (hFactors p.1) p.2
      continuous_toFun := ?_
      map_zero_left := ?_
      map_one_left := ?_ }
  · apply hq.continuous_lift_prod_right
    have hEq :
        (fun p : unitInterval × X =>
          hq.lift (Ht p.1) (hFactors p.1) (q.hom p.2)) = H := by
      funext p
      have hComp := hq.lift_comp (Ht p.1) (hFactors p.1)
      exact congrArg (fun k : C(X, Z) => k p.2) hComp
    rw [hEq]
    exact H.continuous
  · intro y
    obtain ⟨x, rfl⟩ := hq.surjective y
    change hq.lift (Ht 0) (hFactors 0) (q.hom x) = f.hom (q.hom x)
    have hComp := hq.lift_comp (Ht 0) (hFactors 0)
    have hx : hq.lift (Ht 0) (hFactors 0) (q.hom x) = Ht 0 x :=
      congrArg (fun k : C(X, Z) => k x) hComp
    exact hx.trans (h0 x)
  · intro y
    obtain ⟨x, rfl⟩ := hq.surjective y
    change hq.lift (Ht 1) (hFactors 1) (q.hom x) = g.hom (q.hom x)
    have hComp := hq.lift_comp (Ht 1) (hFactors 1)
    have hx : hq.lift (Ht 1) (hFactors 1) (q.hom x) = Ht 1 x :=
      congrArg (fun k : C(X, Z) => k x) hComp
    exact hx.trans (h1 x)

/-- Pointwise evaluation of the descended homotopy on the image of the quotient map. -/
theorem ofQuotientMap_apply
    {X Y Z : TopCat.{u}} (q : X ⟶ Y) (hq : IsQuotientMap q.hom)
    {f g : Y ⟶ Z} (H : C(unitInterval × X, Z))
    (h0 : ∀ x, H (0, x) = f.hom (q.hom x))
    (h1 : ∀ x, H (1, x) = g.hom (q.hom x))
    (hFactors : ∀ t : unitInterval,
      Function.FactorsThrough (fun x => H (t, x)) q.hom)
    (t : unitInterval) (x : X) :
    ofQuotientMap q hq H h0 h1 hFactors (t, q.hom x) = H (t, x) := by
  let Ht : unitInterval → C(X, Z) := fun t =>
    { toFun := fun x => H (t, x)
      continuous_toFun := H.continuous.comp
        (continuous_const.prodMk continuous_id) }
  change hq.lift (Ht t) (hFactors t) (q.hom x) = H (t, x)
  have hComp := hq.lift_comp (Ht t) (hFactors t)
  have hx : hq.lift (Ht t) (hFactors t) (q.hom x) = Ht t x :=
    congrArg (fun k : C(X, Z) => k x) hComp
  have hHt : Ht t x = H (t, x) := rfl
  exact hx.trans hHt

end TopCat.Homotopy
