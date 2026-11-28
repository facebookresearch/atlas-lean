/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Computability.AkraBazzi.RecurrenceFamilies

/-!
# Constant-shift transfer checks
-/

open Filter Asymptotics Finset Real
open scoped Topology

open AkraBazziRecurrence

#check @AkraBazziRecurrence.shift

variable {α : Type*} [Fintype α] [Nonempty α]
variable {T : ℕ → ℝ} {g : ℝ → ℝ} {a b : α → ℝ} {r : α → ℕ → ℕ}

noncomputable example (R : AkraBazziRecurrence T g a b r)
    (hT : ∀ n < R.n₀, 0 < T n + 2)
    (hg : ∀ x ≥ 0, 0 ≤ g x + 2 * (1 - ∑ i, a i))
    (hgpoly : AkraBazziRecurrence.GrowsPolynomially (fun x => g x + 2 * (1 - ∑ i, a i))) :
    AkraBazziRecurrence (fun n => T n + 2) (fun x => g x + 2 * (1 - ∑ i, a i)) a b r :=
  R.shift 2 hT hg hgpoly

example (R : AkraBazziRecurrence T g a b r) (c : ℝ)
    (hf' : 0 ≤ᶠ[atTop] g) (hg' : 0 ≤ᶠ[atTop] fun _ : ℝ => c * (1 - ∑ i, a i)) :
    AkraBazziRecurrence.GrowsPolynomially (fun x => g x + c * (1 - ∑ i, a i)) :=
  AkraBazziRecurrence.GrowsPolynomially.add R.g_grows_poly growsPolynomially_const hf' hg'
