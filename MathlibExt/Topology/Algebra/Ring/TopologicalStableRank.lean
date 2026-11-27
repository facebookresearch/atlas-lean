/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Algebra.Ring.GeneratingTuples
public import Mathlib.Data.ENat.Lattice
public import Mathlib.Data.PNat.Notation
public import Mathlib.Topology.Algebra.Ring.Basic

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Topology.Homeomorph.Lemmas

/-!
# Numeric topological stable rank by dense generators

Let R be a semiring with any topology. For positive n, let Lg_n(R)={a∈R^n:∃c∈R^n,∑i
c_i*a_i=1}, with the finite product topology. Rieffel’s numeric topological stable rank tsr(R)
is the infimum of those positive n for which Lg_n(R) is dense, and ∞ if none exists. Finite
stable-rank bounds are monotone in positive tuple length; the numeric rank is never zero.
-/

public section

open Set

universe u

/-- **Dense left-generating tuples as a stable-rank bound.**

Let R be a semiring with any topology. For positive n, let Lg_n(R)={a∈R^n:∃c∈R^n,∑i
c_i*a_i=1}, with the finite product topology. Rieffel’s numeric topological stable rank tsr(R)
is the infimum of those positive n for which Lg_n(R) is dense, and ∞ if none exists.
HasTopologicalStableRankAtMost R n means Dense(Lg_n(R)) in R^n.
-/
@[expose] def HasTopologicalStableRankAtMost
    (R : Type u) [Semiring R] [TopologicalSpace R]
    (n : ℕ+) : Prop :=
  Dense {a : Fin n → R | IsLeftGeneratingTuple a}

/-- **Monotonicity of positive generating-tuple density.**

Let R be a semiring with any topology. For positive n, let Lg_n(R)={a∈R^n:∃c∈R^n,∑i
c_i*a_i=1}, with the finite product topology. Rieffel’s numeric topological stable rank tsr(R)
is the infimum of those positive n for which Lg_n(R) is dense, and ∞ if none exists. If
Lg_m(R) is dense and 0<m≤n, then Lg_n(R) is dense.
-/
theorem HasTopologicalStableRankAtMost.mono
    {R : Type u} [Semiring R] [TopologicalSpace R]
    {m n : ℕ+} (hm : HasTopologicalStableRankAtMost R m)
    (hmn : m ≤ n) : HasTopologicalStableRankAtMost R n := by
  have hmnNat : (m : ℕ) ≤ (n : ℕ) := hmn
  let d : ℕ := (n : ℕ) - (m : ℕ)
  have hsize : (m : ℕ) + d = (n : ℕ) := Nat.add_sub_of_le hmnNat
  change Dense {a : Fin (n : ℕ) → R | IsLeftGeneratingTuple a}
  rw [← hsize]
  change Dense {a : Fin (m : ℕ) → R | IsLeftGeneratingTuple a} at hm
  let e : ((Fin (m : ℕ) → R) × (Fin d → R)) ≃ₜ
      (Fin ((m : ℕ) + d) → R) :=
    Fin.appendHomeomorph (X := R) (m : ℕ) d
  let generators : Set (Fin (m : ℕ) → R) :=
    {a | IsLeftGeneratingTuple a}
  have hprod : Dense
      (generators ×ˢ (Set.univ : Set (Fin d → R))) :=
    hm.prod dense_univ
  have hpull : Dense
      (e.symm ⁻¹' (generators ×ˢ (Set.univ : Set (Fin d → R)))) :=
    hprod.preimage e.symm.isOpenMap
  refine hpull.mono ?_
  intro x hx
  change IsLeftGeneratingTuple x
  have hxleft : IsLeftGeneratingTuple (e.symm x).1 := hx.1
  obtain ⟨b, hb⟩ := hxleft
  refine ⟨e (b, fun _ => 0), ?_⟩
  rw [← e.apply_symm_apply x]
  change
    (∑ i : Fin ((m : ℕ) + d),
      Fin.append b (fun _ => 0) i *
        Fin.append (e.symm x).1 (e.symm x).2 i) = 1
  rw [Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, zero_mul,
    Finset.sum_const_zero, add_zero]
  exact hb

/-- **Extended-natural numeric topological stable rank.**

Let R be a semiring with any topology. For positive n, let Lg_n(R)={a∈R^n:∃c∈R^n,∑i
c_i*a_i=1}, with the finite product topology. Rieffel’s numeric topological stable rank tsr(R)
is the infimum of those positive n for which Lg_n(R) is dense, and ∞ if none exists. This
extended natural number is topologicalStableRank R.
-/
@[expose] noncomputable def topologicalStableRank
    (R : Type u) [Semiring R] [TopologicalSpace R] : ℕ∞ :=
  ⨅ n : {n : ℕ+ // HasTopologicalStableRankAtMost R n},
    ((n.1 : ℕ) : ℕ∞)

/-- **A dense generating length bounds the numeric rank.**

Let R be a semiring with any topology. For positive n, let Lg_n(R)={a∈R^n:∃c∈R^n,∑i
c_i*a_i=1}, with the finite product topology. Rieffel’s numeric topological stable rank tsr(R)
is the infimum of those positive n for which Lg_n(R) is dense, and ∞ if none exists. If
Lg_n(R) is dense, then topologicalStableRank R≤n.
-/
theorem topologicalStableRank_le_natCast
    (R : Type u) [Semiring R] [TopologicalSpace R]
    (n : ℕ+) (hn : HasTopologicalStableRankAtMost R n) :
    topologicalStableRank R ≤ ((n : ℕ) : ℕ∞) := by
  unfold topologicalStableRank
  exact iInf_le_of_le ⟨n, hn⟩ le_rfl

/-- **Infinite stable rank exactly when no finite generator locus is dense.**

Let R be a semiring with any topology. For positive n, let Lg_n(R)={a∈R^n:∃c∈R^n,∑i
c_i*a_i=1}, with the finite product topology. Rieffel’s numeric topological stable rank tsr(R)
is the infimum of those positive n for which Lg_n(R) is dense, and ∞ if none exists. The rank
is ∞ exactly when Lg_n(R) fails to be dense for every positive n.
-/
theorem topologicalStableRank_eq_top_iff
    (R : Type u) [Semiring R] [TopologicalSpace R] :
    topologicalStableRank R = ⊤ ↔
      ∀ n : ℕ+, ¬ HasTopologicalStableRankAtMost R n := by
  change
    (⨅ n : {n : ℕ+ // HasTopologicalStableRankAtMost R n},
      ((n.1 : ℕ) : ℕ∞)) = ⊤ ↔ _
  constructor
  · intro htop n hn
    let : IsEmpty {n : ℕ+ // HasTopologicalStableRankAtMost R n} :=
      (ENat.iInf_natCast_eq_top.mp htop)
    exact isEmptyElim (⟨n, hn⟩ : {n : ℕ+ // HasTopologicalStableRankAtMost R n})
  · intro hnone
    let : IsEmpty {n : ℕ+ // HasTopologicalStableRankAtMost R n} :=
      ⟨fun n => hnone n.1 n.2⟩
    exact ENat.iInf_eq_top_of_isEmpty

/-- **Numeric topological stable rank is nonzero.**

Let R be a semiring with any topology. For positive n, let Lg_n(R)={a∈R^n:∃c∈R^n,∑i
c_i*a_i=1}, with the finite product topology. Rieffel’s numeric topological stable rank tsr(R)
is the infimum of those positive n for which Lg_n(R) is dense, and ∞ if none exists. The value
topologicalStableRank R is not0, even when it is∞.
-/
theorem topologicalStableRank_ne_zero
    (R : Type u) [Semiring R] [TopologicalSpace R] :
    topologicalStableRank R ≠ 0 := by
  unfold topologicalStableRank
  intro hzero
  rw [ENat.iInf_eq_zero] at hzero
  obtain ⟨n, hn⟩ := hzero
  have hn0 : (n.1 : ℕ) = 0 := ENat.natCast_inj.mp hn
  exact (Nat.ne_of_gt n.1.pos) hn0
