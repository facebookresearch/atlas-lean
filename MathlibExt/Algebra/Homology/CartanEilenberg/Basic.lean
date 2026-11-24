/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.CartanEilenberg.BoundaryCycles
public import MathlibExt.CategoryTheory.Abelian.Projective.Horseshoe

/-!
# Cartan--Eilenberg resolution data

This file packages the two nested horseshoe constructions underlying a
Cartan--Eilenberg resolution of a nonnegatively graded chain complex.  It only
records the chosen projective resolutions and their exact rows; the lifted
chain differential and resulting bicomplex are constructed separately.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/--
The explicit resolution data underlying a Cartan--Eilenberg resolution.

For every degree, the first horseshoe resolves cycles from chosen resolutions of boundaries and
homology.  The second horseshoe then resolves the chain object and literally reuses that chosen
cycle resolution as its left endpoint.
-/
structure CartanEilenbergResolution (L : ChainComplex C ℕ) where
  /-- Chosen projective resolutions of the outgoing boundary objects. -/
  boundaryResolution (j : ℕ) : ProjectiveResolution (L.boundaryFrom j)
  /-- Chosen projective resolutions of the homology objects. -/
  homologyResolution (j : ℕ) : ProjectiveResolution (L.homology j)
  /-- Horseshoe resolutions of the cycle objects. -/
  cyclesHorseshoe (j : ℕ) :
    ProjectiveResolution.HorseshoeData
      (L.boundaryCyclesHomologyShortExact j)
      (boundaryResolution (j + 1)) (homologyResolution j)
  /-- Endpoint coordinates for the chosen cycle horseshoes. -/
  cyclesSpec (j : ℕ) : (cyclesHorseshoe j).Spec
  /-- Horseshoe resolutions of the chain objects, reusing the cycle rows. -/
  termHorseshoe (j : ℕ) :
    ProjectiveResolution.HorseshoeData
      (L.cyclesTermBoundaryShortExact j)
      (cyclesHorseshoe j).middle (boundaryResolution j)
  /-- Endpoint coordinates for the chosen chain-object horseshoes. -/
  termSpec (j : ℕ) : (termHorseshoe j).Spec

namespace CartanEilenbergResolution

variable {L : ChainComplex C ℕ} (P : CartanEilenbergResolution L)

/-- The projective resolution of cycles selected by the first horseshoe. -/
abbrev cyclesResolution (j : ℕ) : ProjectiveResolution (L.cycles j) :=
  (P.cyclesHorseshoe j).middle

/-- The projective resolution of the chain object selected by the second horseshoe. -/
abbrev termResolution (j : ℕ) : ProjectiveResolution (L.X j) :=
  (P.termHorseshoe j).middle

/-- The boundary--cycle--homology row of resolution complexes. -/
abbrev cyclesShortComplex (j : ℕ) :
    ShortComplex (ChainComplex C ℕ) :=
  ShortComplex.mk
    (P.cyclesHorseshoe j).i
    (P.cyclesHorseshoe j).p
    (P.cyclesHorseshoe j).zero

/-- The cycle--term--boundary row of resolution complexes. -/
abbrev termShortComplex (j : ℕ) :
    ShortComplex (ChainComplex C ℕ) :=
  ShortComplex.mk
    (P.termHorseshoe j).i
    (P.termHorseshoe j).p
    (P.termHorseshoe j).zero

/-- The boundary--cycle--homology row of resolution complexes is short exact. -/
theorem cyclesShortExact (j : ℕ) :
    (P.cyclesShortComplex j).ShortExact :=
  (P.cyclesHorseshoe j).shortExact

/-- The cycle--term--boundary row of resolution complexes is short exact. -/
theorem termShortExact (j : ℕ) :
    (P.termShortComplex j).ShortExact :=
  (P.termHorseshoe j).shortExact

/-- Construct Cartan--Eilenberg resolution data from explicit boundary and
homology resolution families. -/
noncomputable def ofResolutions (L : ChainComplex C ℕ)
    (PB : ∀ j : ℕ, ProjectiveResolution (L.boundaryFrom j))
    (PH : ∀ j : ℕ, ProjectiveResolution (L.homology j)) :
    CartanEilenbergResolution L := by
  let HC (j : ℕ) :
      Σ H : ProjectiveResolution.HorseshoeData
          (L.boundaryCyclesHomologyShortExact j) (PB (j + 1)) (PH j),
        H.Spec :=
    (ProjectiveResolution.horseshoe_spec_nonempty
      (L.boundaryCyclesHomologyShortExact j) (PB (j + 1)) (PH j)).some
  let HT (j : ℕ) :
      Σ H : ProjectiveResolution.HorseshoeData
          (L.cyclesTermBoundaryShortExact j) (HC j).1.middle (PB j),
        H.Spec :=
    (ProjectiveResolution.horseshoe_spec_nonempty
      (L.cyclesTermBoundaryShortExact j) (HC j).1.middle (PB j)).some
  exact
    { boundaryResolution := PB
      homologyResolution := PH
      cyclesHorseshoe := fun j => (HC j).1
      cyclesSpec := fun j => (HC j).2
      termHorseshoe := fun j => (HT j).1
      termSpec := fun j => (HT j).2 }

@[simp]
theorem ofResolutions_boundaryResolution (L : ChainComplex C ℕ)
    (PB : ∀ j : ℕ, ProjectiveResolution (L.boundaryFrom j))
    (PH : ∀ j : ℕ, ProjectiveResolution (L.homology j)) (j : ℕ) :
    (ofResolutions L PB PH).boundaryResolution j = PB j :=
  rfl

@[simp]
theorem ofResolutions_homologyResolution (L : ChainComplex C ℕ)
    (PB : ∀ j : ℕ, ProjectiveResolution (L.boundaryFrom j))
    (PH : ∀ j : ℕ, ProjectiveResolution (L.homology j)) (j : ℕ) :
    (ofResolutions L PB PH).homologyResolution j = PH j :=
  rfl

end CartanEilenbergResolution

end HomologicalComplex

end
