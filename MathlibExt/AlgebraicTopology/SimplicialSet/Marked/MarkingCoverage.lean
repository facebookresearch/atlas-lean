/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.SelectedEdges
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.Iso
import Mathlib.CategoryTheory.LiftingProperties.Basic

/-!
# Original coverage of selected marked edges

A map covers the target marking when every original marked target edge
is the image of an original marked source edge. For monomorphisms this
identifies the source marking with the full inherited marking. Coverage
also transports any whole underlying lifting square to a genuine marked
lift, retaining its same diagonal. Minimal markings and selected-edge
images give explicit native coverage criteria.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked

/-- Every original marked target edge has an actual marked source edge with the same whole image. -/
def MarkingSurjective {X Y : Marked.{u}} (f : X ⟶ Y) : Prop :=
  ∀ e : Y.toSSet _⦋1⦌, e ∈ Y.marking →
    ∃ a : X.toSSet _⦋1⦌, a ∈ X.marking ∧ f.hom.app (op ⦋1⦌) a = e

/-- A marking-covering original monomorphism reflects precisely the supplied mark set. -/
theorem MarkingSurjective.reflect {X Y : Marked.{u}} {f : X ⟶ Y} [Mono f]
    (hf : MarkingSurjective f) (e : X.toSSet _⦋1⦌) :
    f.hom.app (op ⦋1⦌) e ∈ Y.marking → e ∈ X.marking := by
  intro he
  obtain ⟨a, ha, h⟩ := hf _ he
  exact (f.injective_app ⦋1⦌ h) ▸ ha

/-- A marking-covering original monomorphism has exactly the marking inherited from its target on its
  original carrier. -/
def MarkingSurjective.sourceComapIso {X Y : Marked.{u}} (f : X ⟶ Y) [Mono f]
    (hf : MarkingSurjective f) : X ≅ comap Y f.hom :=
  isoMk (Iso.refl X.toSSet) (fun e => ⟨fun he => f.preserve he, hf.reflect e⟩)

/-- Native underlying lifts preserve the original whole marked diagonal when the source map covers target marks. -/
theorem MarkingSurjective.hasLiftingProperty {A D X Y : Marked.{u}} {i : A ⟶ D}
    (hi : MarkingSurjective i) (p : X ⟶ Y) [HasLiftingProperty i.hom p.hom] :
    HasLiftingProperty i p := by
  refine ⟨fun {a b} sq => ?_⟩
  let sq' : CommSq a.hom i.hom p.hom b.hom := ⟨congrArg Hom.hom sq.w⟩
  let g : D ⟶ X :=
    { hom := sq'.lift
      preserve {e} he := by
        obtain ⟨x, hx, h⟩ := hi e he
        have hg : sq'.lift.app (op ⦋1⦌) e = a.hom.app (op ⦋1⦌) x := by
          exact (congrArg (sq'.lift.app (op ⦋1⦌)) h).symm.trans
            (ConcreteCategory.congr_hom (congr_app sq'.fac_left (op ⦋1⦌)) x)
        exact hg.symm ▸ a.preserve hx }
  exact CommSq.HasLift.mk' ⟨g, Hom.ext sq'.fac_left, Hom.ext sq'.fac_right⟩

/-- Actual vertex coverage covers all original minimal markings by the same original degeneracy maps. -/
theorem markingSurjective_minimal {A D : SSet.{u}} (f : A ⟶ D)
    (hf : Function.Surjective (f.app (op ⦋0⦌))) : MarkingSurjective (minimal.map f) := by
  intro e he
  obtain ⟨d, hd⟩ := he
  obtain ⟨a, ha⟩ := hf d
  refine ⟨A.σ (0 : Fin 1) a, ⟨a, rfl⟩, ?_⟩
  exact (SSet.σ_naturality_apply f (0 : Fin 1) a).trans ((congrArg (D.σ (0 : Fin 1)) ha).trans hd)

/-- Vertex coverage and the actual selected-edge image condition cover the entire original target marking. -/
theorem markingSurjective_selected {A D : SSet.{u}} {E : Set (A _⦋1⦌)} {F : Set (D _⦋1⦌)}
    (f : withEdges A E ⟶ withEdges D F) (hf : Function.Surjective (f.hom.app (op ⦋0⦌)))
    (hE : ∀ e : D _⦋1⦌, e ∈ F → ∃ a : A _⦋1⦌, a ∈ E ∧ f.hom.app (op ⦋1⦌) a = e) :
    MarkingSurjective f := by
  intro e he
  rcases he with he | he
  · obtain ⟨d, hd⟩ := he
    obtain ⟨a, ha⟩ := hf d
    refine ⟨A.σ (0 : Fin 1) a, Or.inl ⟨a, rfl⟩, ?_⟩
    exact (SSet.σ_naturality_apply f.hom (0 : Fin 1) a).trans ((congrArg (D.σ (0 : Fin 1)) ha).trans hd)
  · obtain ⟨a, ha, h⟩ := hE e he
    exact ⟨a, Or.inr ha, h⟩

end SSet.Marked
