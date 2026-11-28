/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Weak ergodicity: age structures forget their initial condition under changing rates

López (1961) and Coale showed that a population projected by a time-varying sequence of
nonnegative (Leslie-type) matrices `A_0, A_1, …` forgets its initial age structure: for any
two nonzero nonnegative initial vectors, the normalized structures of
`A_{t-1} ⋯ A_0 y_0` and `A_{t-1} ⋯ A_0 y_0'` approach each other, although each may keep
changing in time. The uniform positivity condition is Hajnal's ergodic set, as defined by
Cohen (1982): for `n > 0`, a set of `n × n` nonnegative matrices such that every product of `q`
of them is strictly positive (a primitive set of order `q`) and, for every matrix in the set, the
ratio of its smallest positive entry to its largest entry is at least `R > 0`. For such sets the
Hilbert projective distance between the two projected vectors decays geometrically with constants
that do not depend on the initial vectors (Cohen 1982, p. 482, after Golubitsky, Keeler and
Rothschild 1975).

`Domains.Biology.Demography.Leslie` proves the strong ergodic theorem for a single primitive
Leslie matrix; the time-varying case recorded here is not covered.

Sources: A. López, *Problems in Stable Population Theory*, Office of Population Research,
Princeton (1961), chs. III–IV; J. E. Cohen, "Ergodicity of age structure in populations with
Markovian vital rates, II", Adv. Appl. Probab. 9 (1977) 18–37, p. 19; J. E. Cohen,
"Multiregional age-structured populations with changing rates: weak and stochastic ergodic
theorems" (1982), §3, pp. 481–484, citing J. Hajnal (1976) for ergodic sets and
Golubitsky, Keeler and Rothschild (1975) for the uniform contraction.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

@[expose] public section

namespace WantedExt.Biology.Ecology.WeakErgodicityWanted

open Matrix Filter Topology

variable {n : ℕ}

/-- The forward product `A_{t-1} ⋯ A_1 A_0` of a sequence of projection matrices
(the identity for `t = 0`). -/
def forwardProduct (A : ℕ → Matrix (Fin n) (Fin n) ℝ) : ℕ → Matrix (Fin n) (Fin n) ℝ
  | 0 => 1
  | t + 1 => A t * forwardProduct A t

/-- The `ℓ¹` normalization `y / ∑_i |y_i|` of a population vector (the age structure). -/
noncomputable def normalize (y : Fin n → ℝ) : Fin n → ℝ :=
  (∑ i, |y i|)⁻¹ • y

/-- The **Hilbert projective metric** `d(u, v) = ln (max_i u_i/v_i · max_i v_i/u_i)` between
positive vectors. -/
noncomputable def hilbertMetric (u v : Fin n → ℝ) : ℝ :=
  Real.log (⨆ i, u i / v i) + Real.log (⨆ i, v i / u i)

/-- **Ergodic set.** An ergodic set with parameters `q > 0` and `R > 0` (Hajnal 1976; Cohen 1982,
p. 481) is a set of nonnegative matrices such that every product of `q` matrices from the set is
strictly positive, and every matrix `M` in the set satisfies the entrywise ratio bound
`0 < M i j → R * M k l ≤ M i j` for all indices `i, j, k, l`. For `n > 0` this bound is
`min⁺(M) ≥ R · max(M)`: `primitive` with `q > 0` gives `M` a positive entry, since a nonnegative
`M` with none is `0` and the product of `q` copies of `0` is not positive. For `n = 0` the empty
matrix has no positive entry and every entrywise condition holds vacuously. -/
structure IsErgodicSet (X : Set (Matrix (Fin n) (Fin n) ℝ)) (q : ℕ) (R : ℝ) : Prop where
  pos_q : 0 < q
  pos_R : 0 < R
  nonneg : ∀ M ∈ X, ∀ i j, 0 ≤ M i j
  primitive : ∀ Ms : Fin q → Matrix (Fin n) (Fin n) ℝ, (∀ k, Ms k ∈ X) →
    ∀ i j, 0 < (List.ofFn Ms).prod i j
  ratio : ∀ M ∈ X, ∀ i j k l, 0 < M i j → R * M k l ≤ M i j

/-- **Uniform geometric contraction** (Cohen 1982, p. 482, after Golubitsky, Keeler and
Rothschild 1975). For an ergodic set `X` with parameters `(q, R)` there are constants `D > 0`
and `K ∈ (0, 1)` such that for every sequence of matrices from `X`, all nonzero nonnegative
initial vectors `u, v`, and all `t ≥ q`, the projected vectors are positive and their Hilbert
projective distance is at most `D K^t`.

Source: Cohen (1982), §3, p. 482. -/
public theorem_wanted hilbertMetric_forwardProduct_le (hn : 0 < n)
    {X : Set (Matrix (Fin n) (Fin n) ℝ)} {q : ℕ} {R : ℝ} (hX : IsErgodicSet X q R) :
    ∃ D K : ℝ, 0 < D ∧ 0 < K ∧ K < 1 ∧
      ∀ A : ℕ → Matrix (Fin n) (Fin n) ℝ, (∀ t, A t ∈ X) →
        ∀ u v : Fin n → ℝ, 0 ≤ u → u ≠ 0 → 0 ≤ v → v ≠ 0 → ∀ t, q ≤ t →
          (∀ i, 0 < (forwardProduct A t *ᵥ u) i) ∧ (∀ i, 0 < (forwardProduct A t *ᵥ v) i) ∧
          hilbertMetric (forwardProduct A t *ᵥ u) (forwardProduct A t *ᵥ v) ≤ D * K ^ t

/-- **Weak ergodicity** (López 1961; Cohen 1977, p. 19; Cohen 1982, §3). For any sequence
`A_0, A_1, …` of matrices from an ergodic set and any two nonzero nonnegative initial vectors
`u, v`, the normalized population structures of `A_{t-1} ⋯ A_0 u` and `A_{t-1} ⋯ A_0 v`
converge to each other.

Sources: López (1961), chs. III–IV; Cohen (1977), p. 19; Cohen (1982), §3. -/
public theorem_wanted tendsto_normalize_sub (hn : 0 < n) {X : Set (Matrix (Fin n) (Fin n) ℝ)}
    {q : ℕ} {R : ℝ} (hX : IsErgodicSet X q R) (A : ℕ → Matrix (Fin n) (Fin n) ℝ)
    (hA : ∀ t, A t ∈ X) {u v : Fin n → ℝ} (hu : 0 ≤ u) (hu0 : u ≠ 0) (hv : 0 ≤ v)
    (hv0 : v ≠ 0) :
    Tendsto (fun t => ‖normalize (forwardProduct A t *ᵥ u) - normalize (forwardProduct A t *ᵥ v)‖)
      atTop (𝓝 0)

end WantedExt.Biology.Ecology.WeakErgodicityWanted
