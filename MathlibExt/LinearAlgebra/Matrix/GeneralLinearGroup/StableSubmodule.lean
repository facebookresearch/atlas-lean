/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.Algebra.Module.ZMod
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Subspaces stable under the general linear group

For a field `K` and a finite index type `n`, the only subspaces of `n → K` that are stable under
every invertible matrix are `⊥` and `⊤`
(`Matrix.GeneralLinearGroup.eq_bot_or_eq_top_of_forall_mulVec_mem`). In particular, for a prime
`p`, no subgroup of order `p` of `(ℤ/pℤ)²` is stable under `GL₂(ℤ/pℤ)`
(`Matrix.GeneralLinearGroup.natCard_ne_of_forall_mulVec_mem`).

Gross uses both forms for the `p`-torsion `E_p` of an elliptic curve whose mod `p` Galois image
is all of `GL₂(ℤ/pℤ)`: a stable line would put the Galois group in a Borel subgroup (proof of
Lemma 4.3), and `E_p` is a simple module over `GL₂(ℤ/pℤ)` (proof of Proposition 9.3).

## Proof

Let `W` be stable and contain `v ≠ 0`, say `v j ≠ 0`. For each `i`, applying the transvection
`1 + E_{ij}` if needed gives `u ∈ W` with `u i ≠ 0`, and the invertible matrix `1 - c eᵢᵀ` with
`c = (u i)⁻¹ (u - u i • eᵢ)` (whose square-zero part has `c i = 0`) sends `u` to `u i • eᵢ`. So
`W` contains every standard basis vector and is `⊤`.

## References

* B. H. Gross, *Kolyvagin's work on modular elliptic curves*, in *L-functions and arithmetic*
  (Durham, 1989), London Math. Soc. Lecture Note Ser. 153, Cambridge Univ. Press, 1991,
  235–256: proof of Lemma 4.3, p. 242, and proof of Proposition 9.3, p. 250.
-/

@[expose] public section

open Matrix

namespace Matrix.GeneralLinearGroup

variable {n K : Type*} [Fintype n] [DecidableEq n] [Field K]

/-- A vector `v` with `v i ≠ 0` is sent to `v i • eᵢ` by some invertible matrix. -/
private theorem exists_mulVec_eq_single {v : n → K} {i : n} (hv : v i ≠ 0) :
    ∃ g : GL n K, (g : Matrix n n K) *ᵥ v = Pi.single i (v i) := by
  set c : n → K := (v i)⁻¹ • (v - Pi.single i (v i)) with hc
  have hci : c i = 0 := by simp [hc]
  set N : Matrix n n K := vecMulVec c (Pi.single i 1) with hN
  have hNv : N *ᵥ v = v - Pi.single i (v i) := by
    rw [hN, vecMulVec_mulVec, single_one_dotProduct]
    simp [hc, smul_smul, hv]
  have hNN : N * N = 0 := by
    ext a b
    simp [hN, vecMulVec, Matrix.mul_apply, Pi.single_apply, hci]
  refine ⟨⟨1 - N, 1 + N, ?_, ?_⟩, ?_⟩
  · rw [sub_mul, one_mul, mul_add, mul_one, hNN]
    abel
  · rw [add_mul, one_mul, mul_sub, mul_one, hNN]
    abel
  · change (1 - N) *ᵥ v = _
    rw [sub_mulVec, one_mulVec, hNv]
    abel

/-- **Stable subspaces under `GL_n(K)`.** Let `K` be a field and `n` a finite type. If a subspace
`W` of `n → K` satisfies `g *ᵥ x ∈ W` for every invertible matrix `g` and every `x ∈ W`, then
`W = ⊥` or `W = ⊤`. -/
theorem eq_bot_or_eq_top_of_forall_mulVec_mem (W : Submodule K (n → K))
    (hW : ∀ g : GL n K, ∀ x ∈ W, (g : Matrix n n K) *ᵥ x ∈ W) : W = ⊥ ∨ W = ⊤ := by
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  right
  obtain ⟨v, hvW, hv0⟩ := (Submodule.ne_bot_iff W).mp hbot
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := Function.ne_iff.mp hv0
  have hsingle : ∀ (i : n) (a : K), Pi.single i a ∈ W := by
    intro i a
    obtain ⟨u, huW, hui⟩ : ∃ u ∈ W, u i ≠ 0 := by
      by_cases hvi : v i = 0
      · have hij : i ≠ j := fun h => hj (h ▸ hvi)
        let g : GL n K := GeneralLinearGroup.mkOfDetNeZero (transvection i j 1)
          (by rw [det_transvection_of_ne i j hij]; exact one_ne_zero)
        refine ⟨(g : Matrix n n K) *ᵥ v, hW g v hvW, ?_⟩
        have hg : (g : Matrix n n K) = transvection i j 1 := rfl
        rw [hg, transvection, add_mulVec, one_mulVec]
        simp [hvi, hj, mulVec, dotProduct, single_apply]
      · exact ⟨v, hvW, hvi⟩
    obtain ⟨g, hg⟩ := exists_mulVec_eq_single hui
    have hmem : Pi.single i (u i) ∈ W := hg ▸ hW g u huW
    have : (a * (u i)⁻¹) • Pi.single i (u i) = Pi.single i a := by
      rw [← Pi.single_smul, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hui, mul_one]
    exact this ▸ W.smul_mem _ hmem
  rw [eq_top_iff]
  intro x _
  rw [← Finset.univ_sum_single x]
  exact W.sum_mem fun i _ => hsingle i (x i)

/-- **No line of `(ℤ/pℤ)²` is stable under `GL₂(ℤ/pℤ)`.** Let `p` be a prime. If a subgroup `H`
of `(ℤ/pℤ)²` satisfies `g *ᵥ x ∈ H` for every `g ∈ GL₂(ℤ/pℤ)` and every `x ∈ H`, then `H` does
not have order `p`. -/
theorem natCard_ne_of_forall_mulVec_mem {p : ℕ} [Fact p.Prime]
    (H : AddSubgroup (Fin 2 → ZMod p))
    (hH : ∀ g : GL (Fin 2) (ZMod p), ∀ x ∈ H, (g : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ x ∈ H) :
    Nat.card H ≠ p := by
  have hp := (Fact.out : p.Prime)
  have hW : ∀ g : GL (Fin 2) (ZMod p), ∀ x ∈ AddSubgroup.toZModSubmodule p H,
      (g : Matrix (Fin 2) (Fin 2) (ZMod p)) *ᵥ x ∈ AddSubgroup.toZModSubmodule p H :=
    fun g x hx => (AddSubgroup.mem_toZModSubmodule p).mpr
      (hH g x ((AddSubgroup.mem_toZModSubmodule p).mp hx))
  rcases eq_bot_or_eq_top_of_forall_mulVec_mem (AddSubgroup.toZModSubmodule p H) hW with h | h
  · have hH' : H = ⊥ := (AddSubgroup.toZModSubmodule p).injective (h.trans (map_bot _).symm)
    subst hH'
    rw [AddSubgroup.card_bot]
    exact hp.one_lt.ne
  · have hH' : H = ⊤ := (AddSubgroup.toZModSubmodule p).injective (h.trans (map_top _).symm)
    subst hH'
    rw [AddSubgroup.card_top, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    intro h2
    have : p ^ 2 = p ^ 1 := by rw [h2, pow_one]
    exact absurd (Nat.pow_right_injective hp.two_le this) (by norm_num)

end Matrix.GeneralLinearGroup

end
