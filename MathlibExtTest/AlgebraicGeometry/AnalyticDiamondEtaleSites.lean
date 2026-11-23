/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.AnalyticDiamondEtaleSites
import MathlibExt.AlgebraicGeometry.PerfectoidSliceSites

/-!
# Tests for finite étale maps of Tate pairs, analytic maps and diamond sites

The identity of a Tate pair is finite étale because its plus ring is integrally closed, while a map
whose target plus ring contains an element that is not integral over the source plus ring is not
finite étale, whatever its ring map. Maps of analytic adic spaces pull sections back continuously,
charts identify the topological section rings, and affinoid restriction maps are continuous.
An affine pullback that is empty is allowed by representable finite étaleness. The kernel-pair map
of a v-relation has the source and target maps as its two legs.
-/

open CategoryTheory CategoryTheory.Limits Opposite
open MathlibExt.AlgebraicGeometry.AnalyticTateAdicModels
open MathlibExt.AlgebraicGeometry.AnalyticDiamondEtaleSites
open MathlibExt.AlgebraicGeometry.AffinePerfectoidVSite
open MathlibExt.AlgebraicGeometry.PerfectoidSliceSites
open MathlibExt.AlgebraicGeometry.PerfectoidDiamondModels

namespace MathlibExtTest.AnalyticDiamondEtaleSites

variable {p : ℕ} [Fact p.Prime]

/-- The identity map of a Tate pair. -/
private def tateId (V : TatePair p) : TateRingMap p V V :=
  ⟨RingHom.id V.ring, continuous_id, fun _ h ↦ h⟩

/-- The identity of a Tate pair is finite étale: its plus ring is integrally closed. -/
example (V : TatePair p) : IsFiniteEtalePair p (tateId V) := by
  refine ⟨Module.Finite.self _, inferInstanceAs (Algebra.Etale V.ring V.ring), fun s ↦ ?_⟩
  change s ∈ V.plus ↔ V.plus.subtype.IsIntegralElem s
  constructor
  · intro hs
    exact V.plus.subtype.isIntegralElem_map (x := ⟨s, hs⟩)
  · intro hs
    have := V.plus_integral
    obtain ⟨y, hy⟩ := (IsIntegrallyClosedIn.isIntegral_iff (R := V.plus) (A := V.ring)).mp hs
    rw [← hy]
    exact y.property

/-- A target plus ring with an element not integral over the source plus ring is not finite étale,
whatever the ring map: changing only the plus ring is detected. -/
example {V W : TatePair p} (g : TateRingMap p V W) (s : W.ring) (hs : s ∈ W.plus)
    (hn : ¬ (g.hom.comp V.plus.subtype).IsIntegralElem s) : ¬ IsFiniteEtalePair p g :=
  fun h ↦ hn ((h.2.2 s).mp hs)

/-- Morphisms of analytic adic spaces pull back sections continuously. -/
example {X Y : AnalyticAdicSpace p} (f : X ⟶ Y) : SectionsContinuous f.hom.val :=
  f.hom.property.2

/-- Charts of analytic adic spaces identify the topological section rings of opens inside their
image. -/
example {X : AnalyticAdicSpace p} (C : Chart p X) : SectionsHomeomorphic C.map.val :=
  C.sections

/-- The restriction maps of an affinoid model are continuous for its section topologies. -/
example {P : TatePair p} (M : AffinoidModel p P) {U V : TopologicalSpace.Opens M.valued.space}
    (h : V ≤ U) :
    @Continuous _ _ (M.valued.sectionTopology U) (M.valued.sectionTopology V)
      (M.valued.space.presheaf.map (homOfLE h).op).hom :=
  M.continuous_restrict p h

/-- An empty affine pullback is allowed by representable finite étaleness. -/
example {F G : VSheaf p} (f : F ⟶ G)
    (h : ∀ (Q : Affine p) (a : affineSheaf p Q ⟶ G), Nonempty (IsInitial (pullback f a))) :
    IsRepresentableFiniteEtale p f :=
  fun Q a ↦ Or.inl (h Q a)

/-- The kernel-pair map of a v-relation has the source map as its first leg. -/
example (R : Relation p) :
    relationToKernel p R ≫ pullback.fst (quotientAtlas p R) (quotientAtlas p R) = R.source :=
  relationToKernel_fst p R

/-- The kernel-pair map of a v-relation has the target map as its second leg. -/
example (R : Relation p) :
    relationToKernel p R ≫ pullback.snd (quotientAtlas p R) (quotientAtlas p R) = R.target :=
  relationToKernel_snd p R

end MathlibExtTest.AnalyticDiamondEtaleSites
