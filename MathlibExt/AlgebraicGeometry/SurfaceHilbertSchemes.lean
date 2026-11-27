/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Pullbacks
public import MathlibExt.AlgebraicGeometry.ProjectiveSpace

@[expose] public noncomputable section

/-!
# Hilbert schemes of points on actual surfaces

A family is an actual closed subscheme of X times the parameter scheme
whose projection to the parameter scheme is finite locally free (finite,
flat and locally of finite presentation). Its length is the rank of that
projection at every point of the parameter scheme, `Scheme.Hom.finrank`,
so families over parameter schemes without rational points are
constrained too. The representing property is a cartesian
universal-family condition on all parameter schemes, and contains no
smoothness conclusion. Projective space and projectivity are those of
`ProjectiveSpace`, re-exported here.

Sources: Stacks Project, Hilbert functor, Tags 0D01 and 0DPA, and finite
locally free morphisms, Tags 02K9 and 02KA;
Fogarty, Algebraic Families on an Algebraic Surface.
-/

namespace MathlibExt.AlgebraicGeometry.SurfaceHilbertSchemes

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry

export _root_.MathlibExt.AlgebraicGeometry.ProjectiveSpace (projectiveSpace IsProjective)

universe u

/-- A length-`n` family of closed subschemes of `X` parametrized by `T`: an actual
closed subscheme of the relative product whose projection to `T` is finite
locally free of constant rank `n`, the rank being tested at every point of
`T` (not only at rational points). -/
structure PointSubscheme {k : Type u} [Field k]
    (X T : Over (Spec (.of k))) (n : ℕ) where
  /-- The total space of the family. -/
  Z : Scheme.{u}
  /-- Its closed immersion into the relative product `X ×ₖ T`. -/
  i : Z ⟶ (prod X T).left
  [closed : IsClosedImmersion i]
  [finite : IsFinite (i ≫ (prod.snd : prod X T ⟶ T).left)]
  [flat : Flat (i ≫ (prod.snd : prod X T ⟶ T).left)]
  [finitePresentation :
    LocallyOfFinitePresentation (i ≫ (prod.snd : prod X T ⟶ T).left)]
  /-- The projection has rank `n` at every point of the parameter scheme. -/
  length : ∀ t : T.left, (i ≫ (prod.snd : prod X T ⟶ T).left).finrank t = n

attribute [instance] PointSubscheme.closed PointSubscheme.finite PointSubscheme.flat
  PointSubscheme.finitePresentation

/-- The proper Hilbert representative and its actual universal family. -/
structure HilbertPointsModel {k : Type u} [Field k]
    (X : Over (Spec (.of k))) (n : ℕ) where
  /-- The representing scheme. -/
  H : Over (Spec (.of k))
  [proper : IsProper H.hom]
  /-- The universal length-`n` family over the representing scheme. -/
  universalFamily : PointSubscheme X H n
  /-- Every length-`n` family, over any parameter scheme, is the pullback of the
  universal family along a unique parameter map. -/
  universal : ∀ (T : Over (Spec (.of k))) (Z : PointSubscheme X T n),
    ∃! f : T ⟶ H,
      ∃ a : Z.Z ⟶ universalFamily.Z,
        IsPullback a Z.i universalFamily.i (prod.map (𝟙 X) f).left

end MathlibExt.AlgebraicGeometry.SurfaceHilbertSchemes
