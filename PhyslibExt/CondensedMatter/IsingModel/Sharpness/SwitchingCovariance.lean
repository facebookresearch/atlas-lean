/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.Switching

/-!
# The switching lemma for disconnection events

The switching gap `#{K : ∂K = A} - #{K : ∂K = A ∆ {u, v}}` equals `#{K : ∂K = A}` on `u ↮ v` and
vanishes on `u ↔ v`.

## i. Overview

This is the subtraction form of the switching lemma. Summed over multigraph edge sets with sources
`A`, it writes a difference of double-current sums, which is a covariance after normalization, as a
sum restricted to the disconnection event `u ↮ v`.

## ii. Key results

- `switching_disconnect_card` : the counting identity
- `switching_disconnect_lemma` : the weighted identity
- `srcPairDisconnect_eq` : the summed identity

## iii. Table of contents

- A. The switching gap

## iv. References

- M. Aizenman, "Geometric analysis of φ⁴ fields and Ising models", Comm. Math. Phys. 86 (1982) 1–48
- H. Duminil-Copin, "Random currents expansion of the Ising model", lecture notes (2016),
  arXiv:1607.06933

-/

@[expose] public section

open Finset BigOperators
open scoped symmDiff


namespace StatMech
namespace Sharpness
namespace RandomCurrent

variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]

/-! ## A. The switching gap -/

open Classical in
lemma switching_disconnect_card (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {u v : V} (huv : u ≠ v) :
    (#(m.powerset.filter (fun K => sources ends K = A)) : ℤ)
        - #(m.powerset.filter (fun K => sources ends K = A ∆ {u, v}))
      = (if ¬ connK ends m u v then
          (#(m.powerset.filter (fun K => sources ends K = A)) : ℤ) else 0) := by
  rw [switching_card ends m hnd A hm huv]
  by_cases hconn : connK ends m u v
  · simp [hconn]
  · simp [hconn]

open Classical in
lemma switching_disconnect_lemma (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (A : Finset V) (hm : sources ends m = A)
    {u v : V} (huv : u ≠ v) (F : Finset ι → ℝ) :
    (∑ _K ∈ m.powerset.filter (fun K => sources ends K = A), F m)
        - (∑ _K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {u, v}), F m)
      = ∑ _K ∈ m.powerset.filter (fun K => sources ends K = A),
          F m * (if ¬ connK ends m u v then 1 else 0) := by
  rw [Finset.sum_const, Finset.sum_const, Finset.sum_const]
  rw [switching_card ends m hnd A hm huv]
  by_cases hconn : connK ends m u v
  · simp [hconn]
  · simp [hconn]

open Classical in
lemma srcPairDisconnect_eq (ends : ι → Sym2 V)
    (hnd : ∀ i, ¬ (ends i).IsDiag)
    (A : Finset V) {u v : V} (huv : u ≠ v) (F : Finset ι → ℝ) :
    (∑ m ∈ (Finset.univ.powerset.filter (fun m => sources ends m = A)),
        (∑ _K ∈ m.powerset.filter (fun K => sources ends K = A), F m))
      - (∑ m ∈ (Finset.univ.powerset.filter (fun m => sources ends m = A)),
          (∑ _K ∈ m.powerset.filter (fun K => sources ends K = A ∆ {u, v}), F m))
      = ∑ m ∈ (Finset.univ.powerset.filter (fun m => sources ends m = A)),
          (∑ _K ∈ m.powerset.filter (fun K => sources ends K = A),
              F m * (if ¬ connK ends m u v then 1 else 0)) := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  rw [Finset.mem_filter, Finset.mem_powerset] at hm
  exact switching_disconnect_lemma ends m (fun i _ => hnd i) A hm.2 huv F

end RandomCurrent
end Sharpness
end StatMech
