/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Algebra.Divisibility.Prod
import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.RingTheory.Multiplicity

/-!
# Removing a common power from an integer family

A nonzero family of integers has a common power of any natural number other
than one whose removal leaves some coordinate not divisible by that number.
The index type need not be finite. In particular, this applies directly to
polynomial coefficient functions.

The finite-index statement is from `P2M/Sol/S_flt_regular.lean:1988-2009`
at anthropics/fermats-last-theorem commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`. The proof here is independently
written using Mathlib's monoid multiplicity API, not the source's finite
minimum of valuations. The importing tests retain the exact finite statement.
-/

public section

namespace Int

/-- Remove a common power of `p` from a nonzero integer family. The residual
condition is nondivisibility, not coprimality; `p` may be zero or composite. -/
theorem exists_pow_smul_eq_and_not_dvd {ι : Type*}
    (f : ι → ℤ) (hf : f ≠ 0) (p : ℕ) (hp : p ≠ 1) :
    ∃ (n : ℕ) (f' : ι → ℤ), f = p ^ n • f' ∧ ∃ i, ¬ (p : ℤ) ∣ f' i := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hf
  have hcoord : FiniteMultiplicity (p : ℤ) (f i) :=
    Int.finiteMultiplicity_iff.mpr ⟨by simpa using hp, hi⟩
  have hfin : FiniteMultiplicity (fun _ : ι => (p : ℤ)) f :=
    emultiplicity_lt_top.mp
      ((le_emultiplicity_map (Pi.evalMonoidHom (fun _ : ι => ℤ) i)).trans_lt
        (emultiplicity_lt_top.mpr hcoord))
  obtain ⟨g, hg, hnot⟩ := hfin.exists_eq_pow_mul_and_not_dvd
  refine ⟨multiplicity (fun _ : ι => (p : ℤ)) f, g, ?_, ?_⟩
  · ext j
    simpa only [Pi.mul_apply, Pi.pow_apply, Pi.smul_apply, nsmul_eq_mul,
      Nat.cast_pow] using congrFun hg j
  · simpa only [pi_dvd_iff, not_forall] using hnot

end Int
