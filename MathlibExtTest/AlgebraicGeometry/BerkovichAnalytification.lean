/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.BerkovichAnalytification

/-!
# Tests for valued points of the Berkovich analytification

A point of the analytification evaluates the constant function `a`, pulled back from the ground
field to any open containing its scheme point, to the norm `‖a‖`; mapping a point along a scheme
morphism keeps its evaluations of pulled-back functions; the identity map fixes every point.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory Opposite
open MathlibExt.AlgebraicGeometry.BerkovichAnalytification

noncomputable section

namespace MathlibExtTest.BerkovichAnalytification

variable {K : Type} [NormedField K] {X : AlgebraicScheme K}

/-- The constant function `a` on an open, pulled back from the ground field. -/
private def constant (U : X.left.Opens) (a : K) : Γ(X.left, U) :=
  X.left.presheaf.map (homOfLE le_top).op
    (X.hom.appTop ((Scheme.ΓSpecIso (CommRingCat.of K)).inv a))

/-- An analytic point evaluates a constant to its norm. -/
example (p : Point K X) (U : X.left.Opens) (hp : p.schemePoint ∈ U) (a : K) :
    p.eval (constant U a) hp = ‖a‖ := by
  have h : X.left.evaluation U p.schemePoint hp (constant U a) =
      scalarMap K X p.schemePoint a := by
    rw [constant, ← Scheme.germ_residue, CommRingCat.comp_apply,
      TopCat.Presheaf.germ_res_apply]
    rfl
  rw [Point.eval, h, p.extends_norm]

/-- The identity map fixes every analytic point. -/
example (p : Point K X) : mapPoint (𝟙 X) p = p :=
  mapPoint_id p

/-- A mapped point has the image scheme point. -/
example {Y : AlgebraicScheme K} (f : X ⟶ Y) (p : Point K X) :
    (mapPoint f p).schemePoint = f.left p.schemePoint :=
  rfl

end MathlibExtTest.BerkovichAnalytification
