/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.RingTheory.PhiNModule.NewtonNumber
public import MathlibExt.RingTheory.WittVector.FractionRingValuation

/-!
# Isocrystals as `φ`-modules

Let `p` be a prime and `k` a perfect field of characteristic `p`. An isocrystal over `k` in the
sense of Mathlib (`WittVector.Isocrystal p k V`) is a vector space `V` over
`K₀ = K(p, k) = W(k)[1/p]` with a bijective `φ(p, k)`-semilinear map `Φ(p, k)`, where `φ(p, k)`
is the absolute Frobenius of `K(p, k)`; if `V` is finite-dimensional, it is a `φ`-module in the
sense of Fontaine–Ouyang, that is, a `(φ, N)`-module with `N = 0`
(`WittVector.Isocrystal.toPhiNModule`). The `p`-adic
valuation `WittVector.FractionRing.addValuation p k` of `K(p, k)` is invariant under `φ(p, k)` and
normalized by `v p = 1`, so the results on `(φ, N)`-modules apply with this valuation. For
instance the Newton number of the standard one-dimensional isocrystal of slope `m` is `m`, so the
Newton number of a one-dimensional isocrystal is the slope given by Mathlib's classification
`WittVector.isocrystal_classification` when `k` is algebraically closed.

## Main definitions and results

* `WittVector.Isocrystal.toPhiNModule`: an isocrystal as a `(φ, N)`-module with `N = 0`.
* `WittVector.Isocrystal.newtonNumber_standardOneDimIsocrystal`: the standard one-dimensional
  isocrystal of slope `m` has Newton number `m`.
* `WittVector.Isocrystal.newtonNumber_eq_of_isocrystalEquiv` and
  `WittVector.Isocrystal.exists_newtonNumber_eq`: a one-dimensional isocrystal over an
  algebraically closed field is isomorphic to the standard one of slope its Newton number.

## References

* J.-M. Fontaine and Y. Ouyang, *Theory of p-adic Galois Representations* (book draft, 2022),
  §8.2.1, Definition 8.14, and §8.2.2, Definition 8.18.
-/

@[expose] public section

open Module

open scoped Isocrystal

namespace WittVector

variable (p : ℕ) [Fact p.Prime] (k : Type*) [Field k] [CharP k p] [PerfectRing k p]

/-- The `(φ, N)`-module over `K(p, k)` with monodromy `N = 0` attached to an isocrystal `V`, for
a prime `p` and a perfect field `k` of characteristic `p`: its Frobenius is the Frobenius
`Φ(p, k)` of `V`, semilinear for the absolute Frobenius `φ(p, k)` of `K(p, k)`, and the scalar
in `N φ = p φ N` is `p`. -/
noncomputable def Isocrystal.toPhiNModule (V : Type*) [AddCommGroup V] [Isocrystal p k V] :
    PhiNModule φ(p, k) (p : K(p, k)) V :=
  PhiNModule.ofPhi Φ(p, k)

/-- The standard one-dimensional isocrystal of slope `m` is finite-dimensional over `K(p, k)`. -/
instance (m : ℤ) : FiniteDimensional K(p, k) (StandardOneDimIsocrystal p k m) :=
  inferInstanceAs (FiniteDimensional K(p, k) K(p, k))

/-- For a prime `p`, a perfect field `k` of characteristic `p` and an integer `m`, the Newton
number of the standard one-dimensional isocrystal of slope `m` (on which `Φ(p, k)` is
`x ↦ p ^ m • φ(p, k) x`), for the `p`-adic valuation of `K(p, k)`, is `m`. -/
theorem Isocrystal.newtonNumber_standardOneDimIsocrystal (m : ℤ) :
    (Isocrystal.toPhiNModule p k (StandardOneDimIsocrystal p k m)).newtonNumber
      (FractionRing.addValuation p k) = m := by
  let b : Basis (Fin 1) K(p, k) (StandardOneDimIsocrystal p k m) := Basis.singleton (Fin 1) K(p, k)
  have h := PhiNModule.coe_newtonNumber _ (FractionRing.addValuation_frobenius p k)
    (Isocrystal.toPhiNModule p k (StandardOneDimIsocrystal p k m)) b
  have hdet : b.det ((Isocrystal.toPhiNModule p k (StandardOneDimIsocrystal p k m)).φ ∘ b) =
      (p : K(p, k)) ^ m := by
    rw [Basis.det_apply, Matrix.det_unique, Basis.toMatrix_apply]
    erw [Function.comp_apply, Basis.singleton_apply, Basis.singleton_repr,
      StandardOneDimIsocrystal.frobenius_apply, map_one]
    exact mul_one _
  rw [hdet, FractionRing.addValuation_p_zpow] at h
  exact_mod_cast h

/-- For a prime `p`, a perfect field `k` of characteristic `p` and a finite-dimensional isocrystal
`V`, if `V` is isomorphic (as an isocrystal) to the standard one-dimensional isocrystal of slope
`m`, then the Newton number of `V`, for the `p`-adic valuation of `K(p, k)`, is `m`. -/
theorem Isocrystal.newtonNumber_eq_of_isocrystalEquiv {V : Type*} [AddCommGroup V]
    [Isocrystal p k V] [FiniteDimensional K(p, k) V] {m : ℤ}
    (e : StandardOneDimIsocrystal p k m ≃ᶠⁱ[p, k] V) :
    (Isocrystal.toPhiNModule p k V).newtonNumber (FractionRing.addValuation p k) = m := by
  rw [← Isocrystal.newtonNumber_standardOneDimIsocrystal p k m]
  exact (PhiNModule.newtonNumber_eq_of_linearEquiv _ (FractionRing.addValuation_frobenius p k) _
    _ e.toLinearEquiv fun x => (e.frob_equivariant x).symm).symm

/-- For a prime `p`, an algebraically closed field `k` of characteristic `p` and a
one-dimensional isocrystal `V` over `k`, `V` is isomorphic to the standard one-dimensional
isocrystal whose slope is the Newton number of `V` for the `p`-adic valuation of `K(p, k)`. -/
theorem Isocrystal.exists_newtonNumber_eq (k : Type*) [Field k] [IsAlgClosed k] [CharP k p]
    (V : Type*) [AddCommGroup V] [Isocrystal p k V] (h_dim : finrank K(p, k) V = 1) :
    ∃ m : ℤ, ∃ _ : FiniteDimensional K(p, k) V,
      (Isocrystal.toPhiNModule p k V).newtonNumber (FractionRing.addValuation p k) = m ∧
      Nonempty (StandardOneDimIsocrystal p k m ≃ᶠⁱ[p, k] V) := by
  have : FiniteDimensional K(p, k) V := FiniteDimensional.of_finrank_pos (by omega)
  obtain ⟨m, ⟨e⟩⟩ := isocrystal_classification p k V h_dim
  exact ⟨m, this, Isocrystal.newtonNumber_eq_of_isocrystalEquiv p k e, ⟨e⟩⟩

end WittVector
