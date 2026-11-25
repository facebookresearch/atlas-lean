/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MarkingCoverage
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.ParameterUnderlyingPushout

/-!
# Exact inherited markings of original parameter pushout-products

When the original source map covers every target marked edge, the actual
parameter pushout-product does too: its original second side contains the
same parameter edge and a chosen original marked source edge. For monic
parameter and source maps, the native pushout-product source is therefore
canonically the full target-inherited marking on its original carrier.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked

/-- The original second side covers every target mark of the actual parameter pushout-product. -/
theorem parameterSquare_markingSurjective {A D : SSet.{u}} {X Y : Marked.{u}}
    {a : A ⟶ D} {f : X ⟶ Y} (sq : maxTensorBifunctor.PushoutObjObj f a) (hf : MarkingSurjective f) :
    MarkingSurjective sq.ι := by
  intro e he
  let z : D _⦋1⦌ × Y.toSSet _⦋1⦌ := e
  obtain ⟨x, hx, h⟩ := hf z.2 he.2
  let v : (prod (max D) X).toSSet _⦋1⦌ := (z.1, x)
  refine ⟨sq.inr.hom.app (op ⦋1⦌) v,
    sq.inr.preserve ⟨Set.mem_univ _, hx⟩, ?_⟩
  have hc := ConcreteCategory.congr_hom
    (congr_app (congrArg Hom.hom sq.inr_ι) (op ⦋1⦌)) v
  change sq.ι.hom.app (op ⦋1⦌)
      (sq.inr.hom.app (op ⦋1⦌) v) = z
  exact hc.trans (congrArg (fun y => (z.1, y)) h)

/-- The actual canonical parameter pushout-product retains the full original target mark coverage. -/
theorem parameterPushoutProduct_markingSurjective {A D : SSet.{u}} {X Y : Marked.{u}}
    (a : A ⟶ D) (f : X ⟶ Y) (hf : MarkingSurjective f) :
    MarkingSurjective (parameterPushoutProduct a f) :=
  parameterSquare_markingSurjective (parameterPushout a f) hf

/-- Every native monic parameter square has the full target-inherited marking on its original carrier. -/
def parameterSquareSourceComapIso {A D : SSet.{u}} {X Y : Marked.{u}}
    {a : A ⟶ D} {f : X ⟶ Y} [Mono a] [Mono f] (sq : maxTensorBifunctor.PushoutObjObj f a)
    (hf : MarkingSurjective f) : sq.pt ≅ comap (prod (max D) Y) sq.ι.hom := by
  let _ : Mono sq.ι := parameterSquare_mono sq
  exact (parameterSquare_markingSurjective sq hf).sourceComapIso _

/-- The native monic parameter corner source has exactly the inherited original target marking. -/
def parameterPushoutProductSourceComapIso {A D : SSet.{u}} {X Y : Marked.{u}}
    (a : A ⟶ D) (f : X ⟶ Y) [Mono a] [Mono f] (hf : MarkingSurjective f) :
    (parameterPushout a f).pt ≅ comap (prod (max D) Y) (parameterPushoutProduct a f).hom :=
  parameterSquareSourceComapIso (parameterPushout a f) hf

end SSet.Marked
