/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.DirichletForm.QuasiRegular

import Mathlib.Tactic.Linarith
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Topology.UrysohnsLemma

/-!
# Regular Dirichlet forms are quasi-regular

The main result `isQuasiRegular_of_isRegular` obtains a compact nest from a compact exhaustion
and uses the continuous compactly supported core to give quasi-continuous versions and a
countable family that separates points.
-/

public section

open MeasureTheory Filter Topology Set
open scoped CompactlySupported
open MathlibExt.Probability.DirichletForm

namespace MathlibExt.Probability.DirichletFormWanted

private theorem exists_separating_core {X : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [SecondCountableTopology X] [MeasurableSpace X] {m : Measure X}
    (E : SymmetricForm m) (hreg : E.IsRegular) :
    ∃ (u : ℕ → Lp ℝ 2 m) (f : ℕ → X →C_c ℝ),
      (∀ n, u n ∈ E.domain ∧ (u n : X → ℝ) =ᵐ[m] f n) ∧
        ∀ x y : X, x ≠ y → ∃ n, f n x ≠ f n y := by
  classical
  let Core := {f : X →C_c ℝ // ∃ u ∈ E.domain, (u : X → ℝ) =ᵐ[m] f}
  let : Nonempty Core := ⟨⟨0, 0, E.domain.zero_mem, Lp.coeFn_zero _ _ _⟩⟩
  -- Each core function separates the pairs in an open subset of the product.
  let U (f : Core) : Set (X × X) := {p | f.val p.1 ≠ f.val p.2}
  let S : Set (X × X) := {p | p.1 ≠ p.2}
  have hopen (f : Core) : IsOpen (U f) :=
    isOpen_ne_fun (f.val.continuous.comp continuous_fst) (f.val.continuous.comp continuous_snd)
  have hcover : S ⊆ ⋃ f, U f := by
    rintro ⟨x, y⟩ hxy
    have hdisj : Disjoint ({x} : Set X) {y} := disjoint_singleton.mpr hxy
    obtain ⟨g, hgx, hgy, hg, _⟩ :=
      exists_continuous_one_zero_of_isCompact isCompact_singleton isClosed_singleton hdisj
    obtain ⟨f, hf, hclose⟩ := hreg.2 ⟨g, hg⟩ (1 / 4) (by norm_num)
    have hx : g x = 1 := hgx (mem_singleton x)
    have hy : g y = 0 := hgy (mem_singleton y)
    have hx' : |f x - g x| < 1 / 4 := hclose x
    have hy' : |f y - g y| < 1 / 4 := hclose y
    refine mem_iUnion.mpr ⟨⟨f, hf⟩, fun heq => ?_⟩
    linarith [(abs_lt.mp hx').1, (abs_lt.mp hy').2]
  have hS := HereditarilyLindelofSpace.isLindelof S
  obtain ⟨a, ha⟩ := hS.indexed_countable_subcover U hopen hcover
  choose u hu huf using fun n => (a n).property
  exact ⟨u, fun n => (a n).val, fun n => ⟨hu n, huf n⟩,
    fun x y hxy => mem_iUnion.mp (ha (show (x, y) ∈ S from hxy))⟩

set_option linter.unusedVariables false in
/-- **Regular forms are quasi-regular.** Let `X` be a locally compact separable metric space and `m`
a positive Radon measure on `X`. A regular Dirichlet form on `L²(X; m)` is quasi-regular (M.
Röckner and B. Schmuland, *Quasi-regular Dirichlet forms: examples and counterexamples*, Canad.
J. Math. 47 (1995), Proposition 0.9, stated there for regular semi-Dirichlet forms; cf.
Ma–Röckner 1992, Chapter IV, Example 4a, as cited there). Metrizability cannot be dropped:
Röckner–Schmuland, Remark 0.10 and §5(a), give a regular Dirichlet form on a separable compact
non-metrizable Hausdorff space that is not quasi-regular. -/
theorem isQuasiRegular_of_isRegular {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.MetrizableSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X] {m : Measure X} [IsFiniteMeasureOnCompacts m]
    (E : SymmetricForm m) (hD : E.IsDirichletForm) (hreg : E.IsRegular) : E.IsQuasiRegular := by
  refine ⟨?_, ?_, ?_⟩
  · let K := CompactExhaustion.choice X
    refine ⟨K, ⟨fun _ _ h => K.subset h, K.isClosed, ?_⟩, K.isCompact⟩
    intro u hu ε hε
    obtain ⟨v, hv, ⟨f, hf⟩, huv⟩ := hreg.1 u hu ε hε
    obtain ⟨s, hs, hzero⟩ := exists_compact_iff_hasCompactSupport.mpr f.hasCompactSupport
    obtain ⟨n, hn⟩ := K.exists_superset_of_isCompact hs
    refine ⟨n, v, ⟨hv, ?_⟩, huv⟩
    filter_upwards [hf] with x hx hxK
    exact hx.trans (hzero x (fun hxs => hxK (hn hxs)))
  · refine ⟨{v ∈ E.domain | ∃ f : X →C_c ℝ, (v : X → ℝ) =ᵐ[m] f}, fun _ hv => hv.1,
      fun u hu ε hε => ?_, ?_⟩
    · obtain ⟨v, hv, hf, huv⟩ := hreg.1 u hu ε hε
      exact ⟨v, ⟨hv, hf⟩, huv⟩
    · rintro v ⟨_, f, hf⟩
      exact ⟨f, E.isQuasiContinuous_of_continuous f.continuous, hf⟩
  · obtain ⟨u, f, huf, hsep⟩ := exists_separating_core E hreg
    exact ⟨u, fun n => f n, ∅,
      fun n => ⟨(huf n).1, E.isQuasiContinuous_of_continuous (f n).continuous, (huf n).2⟩,
      E.isExceptional_empty, fun x _ y _ hxy => hsep x y hxy⟩

end MathlibExt.Probability.DirichletFormWanted
