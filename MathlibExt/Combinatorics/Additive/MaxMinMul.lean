/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.NatAntidiagonal

/-!
# Max-min multiplication on coefficient sequences

The max-min product takes the maximum of the pairwise minima at each antidiagonal.
Monotone maps on digits preserve this product and pointwise maximum.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Max-min product.** The max-min product of sequences $g, h \colon \mathbb{N} \to \mathbb{N}$
is the sequence $g \otimes h$ with $(g \otimes h)_k = \max_{i + j = k} \min(g_i, h_j)$ for every
$k \in \mathbb{N}$, the maximum running over pairs of natural numbers $(i, j)$. This is the product
of the max-min semiring $(\mathbb{N}, \max, \min)$ on coefficient sequences.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 1
(the max-min semiring and its polynomials). -/
public def maxMinMul (g h : ℕ → ℕ) : ℕ → ℕ :=
  fun k => (Finset.antidiagonal k).sup fun p => min (g p.1) (h p.2)

/-- **Constant coefficient of a max-min product.** For all sequences
$g, h \colon \mathbb{N} \to \mathbb{N}$, the max-min product satisfies
$(g \otimes h)_0 = \min(g_0, h_0)$.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 1
(the max-min semiring and its polynomials). -/
public theorem maxMinMul_zero (g h : ℕ → ℕ) : maxMinMul g h 0 = min (g 0) (h 0) := by
  simp [maxMinMul]

/-- **Linear coefficient of a max-min product.** For all sequences
$g, h \colon \mathbb{N} \to \mathbb{N}$, the max-min product satisfies
$(g \otimes h)_1 = \max(\min(g_0, h_1), \min(g_1, h_0))$.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Section 1
(the max-min semiring and its polynomials). -/
public theorem maxMinMul_one (g h : ℕ → ℕ) :
    maxMinMul g h 1 = max (min (g 0) (h 1)) (min (g 1) (h 0)) := by
  simp [maxMinMul, Finset.Nat.antidiagonal_succ]

/-- **Monotone digit maps are lunar homomorphisms.** Let $d : \mathbb{N} \to \mathbb{N}$ be
nondecreasing, and for a coefficient sequence $f : \mathbb{N} \to \mathbb{N}$ write $d(f)$ for the
sequence $k \mapsto d(f_k)$. Write $f \oplus g$ for the pointwise maximum and $f \otimes g$ for the
max-min product of coefficient sequences $f$ and $g$. Then for all $f$ and $g$,
$d(f) \oplus d(g) = d(f \oplus g)$ and $d(f) \otimes d(g) = d(f \otimes g)$.

This extends Theorem 15 from zero-preserving base-$b$ digit maps on lunar numbers to arbitrary
nondecreasing maps on $\mathbb{N}$ and all coefficient sequences. The paragraph preceding
Theorem 15 notes that the theory extends to general nondecreasing maps.

Source: Baily, Dell, Fleischmann, Jackson, Pesikoff, Miller and Reifenberg, *Indecomposability
Over the Max-Min Semiring*, Journal of Integer Sequences 28 (2025), Article 25.2.7, Theorem 15
(`jis-2025-25.2.7-thm-15`). -/
public theorem digitMap_lunar_hom {d : ℕ → ℕ} (hd : Monotone d) (f g : ℕ → ℕ) :
    (d ∘ f) ⊔ (d ∘ g) = d ∘ (f ⊔ g) ∧ maxMinMul (d ∘ f) (d ∘ g) = d ∘ maxMinMul f g := by
  constructor
  · funext k
    exact (hd.map_sup (f k) (g k)).symm
  · funext k
    have hk : (Finset.antidiagonal k).Nonempty := ⟨(0, k), by simp⟩
    simpa only [maxMinMul, Function.comp_def, hd.map_min] using
      (Finset.apply_sup_eq_sup_comp_of_nonempty hd hk
        (f := fun p : ℕ × ℕ => min (f p.1) (g p.2))).symm

end -- public section

end MetaMathlibExt
