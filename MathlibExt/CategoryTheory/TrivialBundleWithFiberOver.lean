/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.TrivialBundleWithFiberIso

@[expose] public section

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-!
# Fixed-fiber trivial bundle over a pullback presentation

For an ambient map `p : E ⟶ B`, a base map `f : B' ⟶ B`, and a fixed fiber
`F`, this packages an arbitrary pullback presentation
(`p' : E' ⟶ B'`, `t : E' ⟶ E`, `sq : IsPullback t p' p f`) together with a
fixed-fiber product presentation `TrivialBundleWithFiber F p'` of the pulled
back map. The presentation is arbitrary: no canonical pullback object is
imposed, so one-cell gluing can keep its own chosen total space.

This claims only the fixed fiber `F` over the given base map. It does not
claim a chart over a different base, a global chart over a finite base, or
any model structure.

Iso transport between competing pullback presentations of the same base map
uses the generic `TrivialBundleWithFiber.ofIso` helper. Given a second
pullback square over the same maps and a total-space isomorphism commuting
with the projection to `B'`, the second presentation inherits its
trivialization by `ofIso` while preserving its explicit square.
-/

namespace MorphismProperty

/-- Source-faithful datum used by one-cell gluing: an arbitrary pullback
presentation of `p` along `f`, with fixed fiber `F` trivializing the pulled
back map. -/
structure TrivialBundleWithFiberOver (F : C) {E B : C} (p : E ⟶ B)
    {B' : C} (f : B' ⟶ B) where
  E' : C
  p' : E' ⟶ B'
  t : E' ⟶ E
  sq : IsPullback t p' p f
  trivial : TrivialBundleWithFiber F p'

namespace TrivialBundleWithFiberOver

variable {F : C}

/-- Base change of an over-presentation along a further pullback square.

Given `h` over `f : B' ⟶ B` and a pullback presentation `sq2` of `h.p'`
along `g : B'' ⟶ B'`, this returns the composite presentation over
`g ≫ f`, retaining the ambient map `p` and the explicit pasted square
`sq2.paste_horiz h.sq`. The new trivialization is the parent pullback
`h.trivial.pullback sq2`; the fiber `F` is unchanged. -/
noncomputable def baseChange {E B B' B'' : C} {p : E ⟶ B}
    {f : B' ⟶ B} {g : B'' ⟶ B'} (h : TrivialBundleWithFiberOver F p f)
    {E'' : C} {q : E'' ⟶ B''} {s : E'' ⟶ h.E'}
    (sq2 : IsPullback s q h.p' g) :
    TrivialBundleWithFiberOver F p (g ≫ f) where
  E' := E''
  p' := q
  t := s ≫ h.t
  sq := sq2.paste_horiz h.sq
  trivial := h.trivial.pullback sq2

/-- Iso transport between competing pullback presentations.

Given `h` over `f : B' ⟶ B` and a second pullback presentation `sq2` of `p`
along the same `f`, plus an isomorphism `e` of total objects with
`e.hom ≫ h.p' = q`, this returns the second presentation over the same `f`,
preserving the explicit square `sq2`. The new trivialization is
`TrivialBundleWithFiber.ofIso e heq h.trivial`; the fiber `F` is unchanged. -/
noncomputable def ofIso {E B B' : C} {p : E ⟶ B} {f : B' ⟶ B}
    (h : TrivialBundleWithFiberOver F p f)
    {E'' : C} {q : E'' ⟶ B'} {s : E'' ⟶ E}
    (sq2 : IsPullback s q p f) (e : E'' ≅ h.E')
    (heq : e.hom ≫ h.p' = q) :
    TrivialBundleWithFiberOver F p f where
  E' := E''
  p' := q
  t := s
  sq := sq2
  trivial := TrivialBundleWithFiber.ofIso e heq h.trivial

/-- Canonical-pullback consumer: transport to the canonical pullback projection.

Given `h` over `f : B' ⟶ B`, this returns a fixed-fiber presentation of the
canonical `Limits.pullback.snd p f` with the same fiber `F`, via the unique
isomorphism `(h.sq.isoIsPullback _ _ (IsPullback.of_hasPullback p f)).symm`
and the exact commuting equation
`(h.sq.isoIsPullback _ _ _).inv ≫ h.p' = Limits.pullback.snd p f`
(`IsPullback.isoIsPullback_inv_snd`). The ambient square is retained as the
source of the iso; no product limit is reproved. -/
noncomputable def toCanonical {E B B' : C} {p : E ⟶ B} {f : B' ⟶ B}
    (h : TrivialBundleWithFiberOver F p f) [Limits.HasPullback p f] :
    TrivialBundleWithFiber F (Limits.pullback.snd p f) :=
  TrivialBundleWithFiber.ofIso
    (h.sq.isoIsPullback _ _ (IsPullback.of_hasPullback p f)).symm
    (h.sq.isoIsPullback_inv_snd _ _ (IsPullback.of_hasPullback p f))
    h.trivial

/-- Fiber-side transport of an over-presentation along a fiber isomorphism.

Given `e : F ≅ G` and `h` over `f` with fixed fiber `G`, this returns the same
pullback presentation (`h.E'`, `h.p'`, `h.t`, `h.sq`) with fixed fiber `F` via
`h.trivial.mapFiber e`. Only the supplied fiber iso changes the fiber; the base
map, ambient map, and explicit square are unchanged. No gluing, descent, chart,
or model claim is made. -/
noncomputable def mapFiber {E B B' G : C} {p : E ⟶ B} {f : B' ⟶ B}
    (e : F ≅ G) (h : TrivialBundleWithFiberOver G p f) :
    TrivialBundleWithFiberOver F p f where
  E' := h.E'
  p' := h.p'
  t := h.t
  sq := h.sq
  trivial := h.trivial.mapFiber e

/-- Forward ambient transport of an over-presentation along an ambient pullback.

Given `h` over `f_old : B' ⟶ B_old`, an ambient pullback `sqA` presenting
`p_new` as the pullback of `p_old` along `b`, a base compatibility
`hBase : f_new ≫ b = g ≫ f_old`, and a pullback `sq2` of `h.p'` along `g`,
this returns the composite presentation over `f_new : B'' ⟶ B_new` with the
same fiber `F`. The new trivialization is the parent pullback
`h.trivial.pullback sq2`; the new square is the left cancellation
`IsPullback.of_right'` of the pasted outer against `sqA`. No global chart,
monodromy, Serre, weak-equivalence, model, or KQ3 claim is made. -/
noncomputable def forwardOfAmbientPullback {E_old B_old E_new B_new B' B'' : C}
    {p_old : E_old ⟶ B_old} {p_new : E_new ⟶ B_new}
    {f_old : B' ⟶ B_old} {f_new : B'' ⟶ B_new}
    (h : TrivialBundleWithFiberOver F p_old f_old)
    {e : E_new ⟶ E_old} {b : B_new ⟶ B_old}
    (sqA : IsPullback e p_new p_old b)
    {g : B'' ⟶ B'} (hBase : f_new ≫ b = g ≫ f_old)
    {E'' : C} {q : E'' ⟶ B''} {s : E'' ⟶ h.E'}
    (sq2 : IsPullback s q h.p' g) :
    TrivialBundleWithFiberOver F p_new f_new where
  E' := E''
  p' := q
  t := sqA.lift (s ≫ h.t) (q ≫ f_new) (by
    calc (s ≫ h.t) ≫ p_old = s ≫ (h.t ≫ p_old) := by rw [Category.assoc]
      _ = s ≫ (h.p' ≫ f_old) := by rw [h.sq.w]
      _ = (s ≫ h.p') ≫ f_old := by rw [← Category.assoc]
      _ = (q ≫ g) ≫ f_old := by rw [sq2.w]
      _ = q ≫ (g ≫ f_old) := by rw [Category.assoc]
      _ = q ≫ (f_new ≫ b) := by rw [← hBase]
      _ = (q ≫ f_new) ≫ b := by rw [← Category.assoc])
  sq := IsPullback.of_right' (by rw [hBase]; exact sq2.paste_horiz h.sq) sqA
  trivial := h.trivial.pullback sq2

end TrivialBundleWithFiberOver

end MorphismProperty

end CategoryTheory
