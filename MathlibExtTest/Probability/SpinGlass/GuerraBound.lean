/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.SpinGlass.GuerraBound

/-!
# Tests for Guerra's bound for the SK model

Applications of `freeEnergy_le_parisiFunctional` (every size `N ≥ 1`) and
`freeEnergy_le_parisiFunctional_eventually`:

* at a fixed size `N ≥ 1` and for every `β`, the replica-symmetric parameters bound `F_N`, also
  checked on a concrete instance with `β < 0`;
* the replica-symmetric parameters `k = 1`, `m = (0, 1)`, `q = (0, q₁, 1)` give Guerra's
  replica-symmetric bound, also checked on a concrete instance;
* two choices of parameters combine, so that eventually `F_N` lies below the smaller of the two
  Parisi functionals, up to `ε`;
* the bound also holds with a strict inequality, by applying it with `ε / 2`.
-/

@[expose] public section

namespace MathlibExtTest.Probability.GuerraBound

open Filter MathlibExt.Probability.SherringtonKirkpatrick MathlibExt.Probability.ParisiFormulaWanted

/-- Guerra's bound at a fixed size `N ≥ 1` for the replica-symmetric parameters `m = (0, 1)`,
`q = (0, q₁, 1)`, with no condition on `β`. -/
theorem freeEnergy_le_replicaSymmetric_of_pos (β h : ℝ) {N : ℕ} (hN : 0 < N) {q₁ : ℝ}
    (h0 : 0 ≤ q₁) (h1 : q₁ ≤ 1) :
    freeEnergy β h N ≤
      parisiFunctional (skCovariance β) h 1 (fun ℓ => if ℓ = 0 then 0 else 1)
        (fun ℓ => if ℓ = 0 then 0 else if ℓ = 1 then q₁ else 1) :=
  freeEnergy_le_parisiFunctional β h hN (isParisiParameter_replicaSymmetric h0 h1)

/-- A concrete instance at a fixed size and a negative inverse temperature: `β = -2`, `h = 1`,
`N = 3` and `q₁ = 1 / 2`. -/
example : freeEnergy (-2) 1 3 ≤
    parisiFunctional (skCovariance (-2)) 1 1 (fun ℓ => if ℓ = 0 then 0 else 1)
      (fun ℓ => if ℓ = 0 then 0 else if ℓ = 1 then 1 / 2 else 1) :=
  freeEnergy_le_replicaSymmetric_of_pos (-2) 1 (by norm_num) (by norm_num) (by norm_num)

/-- Guerra's bound for the replica-symmetric parameters `m = (0, 1)`, `q = (0, q₁, 1)`. -/
theorem freeEnergy_le_replicaSymmetric (β h : ℝ) (hβ : 0 < β) {q₁ : ℝ} (h0 : 0 ≤ q₁)
    (h1 : q₁ ≤ 1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, freeEnergy β h N ≤
      parisiFunctional (skCovariance β) h 1 (fun ℓ => if ℓ = 0 then 0 else 1)
        (fun ℓ => if ℓ = 0 then 0 else if ℓ = 1 then q₁ else 1) + ε :=
  freeEnergy_le_parisiFunctional_eventually β h hβ (isParisiParameter_replicaSymmetric h0 h1) hε

/-- A concrete instance: `β = 1`, `h = 0`, `q₁ = 1 / 2` and `ε = 1`. -/
example : ∀ᶠ N : ℕ in atTop, freeEnergy 1 0 N ≤
    parisiFunctional (skCovariance 1) 0 1 (fun ℓ => if ℓ = 0 then 0 else 1)
      (fun ℓ => if ℓ = 0 then 0 else if ℓ = 1 then 1 / 2 else 1) + 1 :=
  freeEnergy_le_replicaSymmetric 1 0 one_pos (by norm_num) (by norm_num) one_pos

/-- Two choices of parameters: eventually `F_N` lies below the smaller of the two Parisi
functionals, up to `ε`. -/
theorem freeEnergy_le_min_parisiFunctional (β h : ℝ) (hβ : 0 < β) {k k' : ℕ}
    {m q m' q' : ℕ → ℝ} (hp : IsParisiParameter k m q) (hp' : IsParisiParameter k' m' q')
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, freeEnergy β h N ≤
      min (parisiFunctional (skCovariance β) h k m q)
        (parisiFunctional (skCovariance β) h k' m' q') + ε := by
  filter_upwards [freeEnergy_le_parisiFunctional_eventually β h hβ hp hε,
    freeEnergy_le_parisiFunctional_eventually β h hβ hp' hε] with N h1 h2
  exact (le_min h1 h2).trans (min_add_add_right _ _ _).le

/-- The strict form: eventually `F_N < P_k(m, q) + ε`. -/
theorem freeEnergy_lt_parisiFunctional_eventually (β h : ℝ) (hβ : 0 < β) {k : ℕ}
    {m q : ℕ → ℝ} (hp : IsParisiParameter k m q) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, freeEnergy β h N < parisiFunctional (skCovariance β) h k m q + ε := by
  filter_upwards [freeEnergy_le_parisiFunctional_eventually β h hβ hp (half_pos hε)] with N hN
  linarith

end MathlibExtTest.Probability.GuerraBound
