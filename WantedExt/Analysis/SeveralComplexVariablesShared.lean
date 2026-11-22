/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Shared definitions for the Several Complex Variables Problem List entries

Definitions used by the `WantedExt` modules for problems of the Several Complex Variables Problem
List (Buzzard, Fornaess, Gavosto, Krantz, arXiv:math/9509202). `WantedExt` cannot import
`OpenConjectures`: `lakefile.toml` and `scripts/check_health.sh` let it import only `MathlibExt`,
`CSLibExt` and `PhyslibExt`. The definitions below are therefore copies, under the same names and
with the same bodies, of the open entries that introduced them (as
`WantedExt.GroupTheory.BranchGroupShared` repeats the definitions of an OpenConjectures entry):

* `IsFatouBieberbachDomain`, `IsPseudoconvexDomain`: from
  `OpenConjectures/Analysis/FatouBieberbachIntermediatePseudoconvex/Statement.lean`;
* `fatouSet`: from `OpenConjectures/Analysis/SCVHenonFatouComponents/Statement.lean`.
-/

module

public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Connected.Basic

@[expose] public section

namespace MathlibExt.Analysis.SeveralComplexVariablesShared

open Filter Topology

/-- Fatou-Bieberbach domain in `ℂⁿ`: nonempty open connected proper subset biholomorphic to the
whole space via mutually inverse holomorphic maps (copy of
`OpenConjectures.Analysis.FatouBieberbachIntermediatePseudoconvex.IsFatouBieberbachDomain`). -/
def IsFatouBieberbachDomain (n : ℕ) (Ω : Set (Fin n → ℂ)) : Prop :=
  Ω.Nonempty ∧
    IsOpen Ω ∧
      IsConnected Ω ∧
        Ω ≠ Set.univ ∧
          (∃ f : (Fin n → ℂ) → (Fin n → ℂ), ∃ g : (Fin n → ℂ) → (Fin n → ℂ),
            DifferentiableOn ℂ f Set.univ ∧
              DifferentiableOn ℂ g Ω ∧
                Set.MapsTo f Set.univ Ω ∧
                  ((∀ x, g (f x) = x) ∧ ∀ y ∈ Ω, f (g y) = y))

/-- Pseudoconvex domain in `ℂⁿ`: nonempty open connected set whose holomorphic hulls of compacts
remain compact (holomorphic-convexity encoding of pseudoconvexity; copy of
`OpenConjectures.Analysis.FatouBieberbachIntermediatePseudoconvex.IsPseudoconvexDomain`). For open
subsets of `ℂⁿ`, holomorphic convexity, pseudoconvexity and being Stein are equivalent (solution of
the Levi problem). -/
def IsPseudoconvexDomain (n : ℕ) (Ω : Set (Fin n → ℂ)) : Prop :=
  Ω.Nonempty ∧
    IsOpen Ω ∧
      IsConnected Ω ∧
        (∀ K : Set (Fin n → ℂ), K ⊆ Ω → IsCompact K →
          IsCompact { z ∈ Ω |
            ∀ f : (Fin n → ℂ) → ℂ, DifferentiableOn ℂ f Ω →
              ‖f z‖ ≤ sSup ((fun x => ‖f x‖) '' K) })

/-- The Fatou set of a self-map `F` of `ℂ²`: points near which the forward iterates of `F` are
uniformly bounded (copy of `OpenConjectures.Analysis.SCVHenonFatouComponents.fatouSet`; this is the
definition of the Fatou set in Problem 65 of the problem list). -/
def fatouSet (F : (Fin 2 → ℂ) → Fin 2 → ℂ) : Set (Fin 2 → ℂ) :=
  {z | ∃ U ∈ 𝓝 z, ∃ M : ℝ, ∀ k : ℕ, ∀ w ∈ U, ‖F^[k] w‖ ≤ M}

end MathlibExt.Analysis.SeveralComplexVariablesShared
