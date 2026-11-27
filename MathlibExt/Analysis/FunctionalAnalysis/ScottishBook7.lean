/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Homeomorph.Defs
public import Mathlib.Analysis.Normed.Group.Defs
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Convex.Basic
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Analysis.Convex.TotallyBounded
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! # A counterexample to Scottish Book Problem 7 -/

@[expose] public section

open Filter Set
open scoped Topology ENNReal

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook7Wanted

/-- **Scottish Book Problem 7 (Mazur–Banach).** The claim that in every real Banach space $E$,
any two closed convex subsets $A, B \subseteq E$ whose linear spans are infinite-dimensional are
homeomorphic, with the subspace topologies. -/
def ScottishBookProblem7Claim : Prop :=
  ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (A B : Set E), IsClosed A → Convex ℝ A →
    ¬ Module.Finite ℝ ↥(Submodule.span ℝ A) → IsClosed B → Convex ℝ B →
    ¬ Module.Finite ℝ ↥(Submodule.span ℝ B) → Nonempty (↥A ≃ₜ ↥B)

private abbrev SequenceHilbert := lp (fun _ : ℕ => ℝ) 2

private noncomputable def smallCoordinates (n : ℕ) : SequenceHilbert :=
  lp.single 2 n (1 / ((n : ℝ) + 1))

private theorem smallCoordinates_tendsto : Tendsto smallCoordinates atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hn (n : ℕ) : ‖smallCoordinates n‖ = 1 / ((n : ℝ) + 1) := by
    rw [smallCoordinates, lp.norm_single (by norm_num : (0 : ℝ≥0∞) < 2), Real.norm_eq_abs,
      abs_of_nonneg (by positivity)]
  simpa only [hn] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)

private theorem smallCoordinates_linearIndependent : LinearIndependent ℝ smallCoordinates := by
  let L : SequenceHilbert →ₗ[ℝ] (ℕ → ℝ) := (lpSubmodule ℝ (fun _ : ℕ => ℝ) 2).subtype
  apply LinearIndependent.of_comp L
  have he : (L ∘ smallCoordinates) = fun n : ℕ => Pi.single n (1 / ((n : ℝ) + 1)) := by
    funext n j
    change (lp.single 2 n (1 / ((n : ℝ) + 1)) : SequenceHilbert) j = _
    rw [lp.single_apply]
  rw [he]
  exact Pi.linearIndependent_single_of_ne_zero (R := ℝ) (fun n => by positivity)

private theorem infinite_span_of_contains_smallCoordinates {S : Set SequenceHilbert}
    (hS : range smallCoordinates ⊆ S) : ¬ Module.Finite ℝ ↥(Submodule.span ℝ S) := by
  intro hfin
  let _ : Module.Finite ℝ ↥(Submodule.span ℝ S) := hfin
  let v (n : ℕ) : Submodule.span ℝ S := ⟨smallCoordinates n, Submodule.subset_span (hS ⟨n, rfl⟩)⟩
  have hv : LinearIndependent ℝ v :=
    LinearIndependent.of_comp (Submodule.span ℝ S).subtype smallCoordinates_linearIndependent
  exact Module.Finite.not_linearIndependent_of_infinite v hv

private theorem exists_compact_convex_infinite_span :
    ∃ A : Set SequenceHilbert, IsCompact A ∧ Convex ℝ A ∧
      ¬ Module.Finite ℝ ↥(Submodule.span ℝ A) := by
  let S : Set SequenceHilbert := insert 0 (range smallCoordinates)
  let A := closure (convexHull ℝ S)
  have hS : IsCompact S := smallCoordinates_tendsto.isCompact_insert_range
  have hsub : range smallCoordinates ⊆ A :=
    (subset_insert _ _).trans ((subset_convexHull ℝ S).trans subset_closure)
  exact ⟨A, hS.totallyBounded.convexHull.closure.isCompact_of_isClosed isClosed_closure,
    (convex_convexHull ℝ S).closure, infinite_span_of_contains_smallCoordinates hsub⟩

/--
**Scottish Book Problem 7 fails: closed convex sets need not be homeomorphic.** The Scottish Book
Problem 7 claim is false: there are a real Banach space $E$ and closed convex subsets
$A, B \subseteq E$, each with infinite-dimensional linear span, that are not homeomorphic.

For example, a compact infinite-dimensional closed convex set, such as the Hilbert cube, is not
homeomorphic to a noncompact one, such as the whole space, since compactness is a topological
invariant.

Source:
S. Mazur and S. Banach, Problem 7 of the Scottish Book; T. Banakh's
observation as reported in the 2026 survey "90+ years of the Scottish Book"
(arXiv:2603.27867). The modified classification problem was solved for
Frechet spaces by Banakh-Cauty, Studia Mathematica 205 (2011) 1-11.
-/
public theorem closedConvexSetsHomeomorphic_refuted : ¬ ScottishBookProblem7Claim := by
  intro h
  obtain ⟨A, hAc, hAv, hAfin⟩ := exists_compact_convex_infinite_span
  have hBfin : ¬ Module.Finite ℝ ↥(Submodule.span ℝ (univ : Set SequenceHilbert)) :=
    infinite_span_of_contains_smallCoordinates (subset_univ _)
  obtain ⟨f⟩ := h SequenceHilbert A univ hAc.isClosed hAv hAfin isClosed_univ convex_univ hBfin
  let _ : CompactSpace A := isCompact_iff_compactSpace.mp hAc
  have hE : CompactSpace SequenceHilbert :=
    (f.trans (Homeomorph.Set.univ SequenceHilbert)).compactSpace
  have hne : smallCoordinates 0 ≠ 0 := by
    intro he
    have hcoord := congrArg (fun v : SequenceHilbert => v 0) he
    norm_num [smallCoordinates, lp.single_apply_self, lp.coeFn_zero] at hcoord
  let _ : Nontrivial SequenceHilbert := ⟨⟨smallCoordinates 0, 0, hne⟩⟩
  have hn : NoncompactSpace SequenceHilbert := NormedSpace.noncompactSpace ℝ SequenceHilbert
  exact (not_compactSpace_iff.mpr hn) hE

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook7Wanted
