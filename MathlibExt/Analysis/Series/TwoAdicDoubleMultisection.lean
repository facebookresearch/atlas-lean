/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.PadicValNat
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# Double two-adic multisection of a double series

`tsum_twoAdic_double_multisection` regroups a double series $\sum_{p, q \ge 1} b_{p,q}$ along
the factorizations $p = c 2^j$ and $q = d 2^k$ with $c, d \ge 1$: each term $b_{c 2^j, d 2^k}$
gets the weight $2^{j+k}$, with sign $+$ when $c$ and $d$ have the same parity and $-$ otherwise,
provided the four families so obtained are summable.

The proof regroups each of the four families along its index map. For $j, n \ge 0$, the odd
index $(2n + 1) 2^j$ reaches every positive integer $p$ exactly once, with $j = \nu_2(p)$; the
even index $(2n + 2) 2^j$ reaches $p$ once for each $j < \nu_2(p)$. So the weight that lands on
$b_{p,q}$ factors as $(2^v - \sum_{i < v} 2^i)(2^w - \sum_{i < w} 2^i) = 1$, where
$v = \nu_2(p)$ and $w = \nu_2(q)$.

`tsum_twoAdic_parametric_multisection` is an absolutely summable formulation of Vignat and
Milgram's equation (30). It assumes absolute summability of each weighted family; convergence of
the unweighted series alone does not ensure this. The proof uses the same index maps for a single
series, with a complex weight parameter. The even-index contribution is subtracted, and its finite
geometric sum reduces the net weight to one without dividing by the parameter minus one.

## References

* Christophe Vignat and Michael Milgram, *Curious Multisection Identities by Index Factorization*,
  Journal of Integer Sequences 27 (2024), Article 24.5.5, pp. 1–37. Proposition 1, equation (30),
  gives the parametric series identity; Proposition 8, equation (49) and its proof in Section 4
  give the weighted regrouping. Proposition 15, equation (102), gives the double-series identity.
-/

namespace MetaMathlibExt
namespace tsum_twoAdic_double_multisection

/-- The odd indices `(2n + 1) 2^j`, shifted down by one, enumerate `ℕ` bijectively; the target is
written as a sigma type whose fibres are singletons. -/
private def oddEquiv : ℕ × ℕ ≃ Σ _ : ℕ, Unit where
  toFun x := ⟨(2 * x.2 + 1) * 2 ^ x.1 - 1, ()⟩
  invFun p := (padicValNat 2 (p.1 + 1), (p.1 + 1).divMaxPow 2 / 2)
  left_inv := by
    rintro ⟨j, n⟩
    have hpos : 0 < (2 * n + 1) * 2 ^ j := by positivity
    have hparts : Nat.maxPowDvdDiv 2 ((2 * n + 1) * 2 ^ j) = (j, 2 * n + 1) :=
      Nat.maxPowDvdDiv_of_pow_mul_eq hpos.ne' (Nat.mul_comm _ _) (by omega)
    simp [Nat.sub_add_cancel hpos, padicValNat, Nat.divMaxPow, hparts]
    omega
  right_inv := by
    rintro ⟨p, ⟨⟩⟩
    have hodd : ¬ 2 ∣ (p + 1).divMaxPow 2 := Nat.not_dvd_divMaxPow (by decide) p.succ_ne_zero
    have h : 2 * ((p + 1).divMaxPow 2 / 2) + 1 = (p + 1).divMaxPow 2 := by omega
    simp [h]

private theorem lt_padicValNat_even (j n : ℕ) :
    j < padicValNat 2 ((2 * n + 2) * 2 ^ j - 1 + 1) := by
  have hpos : 0 < (2 * n + 2) * 2 ^ j := by positivity
  rw [Nat.sub_add_cancel hpos, Nat.padicValNat_def, ← Nat.add_one_le_iff,
    ← Nat.pow_dvd_iff_le_multiplicity (by decide) hpos.ne']
  exact ⟨n + 1, by ring⟩

/-- The even indices `(2n + 2) 2^j`, shifted down by one: the index `P` is reached once for each
exponent `j` below the two-adic valuation of `P + 1`, which labels the fibre over `P`. -/
private def evenEquiv : ℕ × ℕ ≃ Σ P : ℕ, Fin (padicValNat 2 (P + 1)) where
  toFun x := ⟨(2 * x.2 + 2) * 2 ^ x.1 - 1, ⟨x.1, lt_padicValNat_even x.1 x.2⟩⟩
  invFun p := (p.2, (p.1 + 1) / 2 ^ ((p.2 : ℕ) + 1) - 1)
  left_inv := by
    rintro ⟨j, n⟩
    have hpos : 0 < (2 * n + 2) * 2 ^ j := by positivity
    have h : (2 * n + 2) * 2 ^ j = (n + 1) * 2 ^ (j + 1) := by ring
    dsimp only
    rw [Nat.sub_add_cancel hpos, h, Nat.mul_div_cancel _ (by positivity), Nat.add_sub_cancel]
  right_inv := by
    rintro ⟨P, i⟩
    have hval : (2 * ((P + 1) / 2 ^ ((i : ℕ) + 1) - 1) + 2) * 2 ^ (i : ℕ) - 1 = P := by
      have hi := i.2
      generalize (i : ℕ) = k at hi ⊢
      obtain ⟨Q, hQ⟩ : 2 ^ (k + 1) ∣ P + 1 := by
        rw [Nat.pow_dvd_iff_le_multiplicity (by decide) P.succ_ne_zero, ← Nat.padicValNat_def]
        exact hi
      obtain ⟨Q, rfl⟩ : ∃ Q', Q = Q' + 1 := ⟨Q - 1, by rcases Q with _ | Q <;> simp_all⟩
      rw [hQ, Nat.mul_div_cancel_left _ (by positivity), Nat.add_sub_cancel,
        show (2 * Q + 2) * 2 ^ k = 2 ^ (k + 1) * (Q + 1) by ring, ← hQ, Nat.add_sub_cancel]
    exact Sigma.ext hval
      ((Fin.heq_ext_iff (congrArg (fun t => padicValNat 2 (t + 1)) hval)).2 rfl)

/-- Pair two sigma types over `ℕ` into one sigma type over `ℕ × ℕ`. -/
private def sigmaProdEquiv (α β : ℕ → Type) :
    (Σ y : ℕ × ℕ, α y.1 × β y.2) ≃ (Σ P, α P) × (Σ Q, β Q) where
  toFun z := (⟨z.1.1, z.2.1⟩, ⟨z.1.2, z.2.2⟩)
  invFun w := (⟨(w.1.1, w.2.1), (w.1.2, w.2.2)⟩ : Σ y : ℕ × ℕ, α y.1 × β y.2)
  left_inv _ := rfl
  right_inv _ := rfl

/-- Regroup a double family with weight `2 ^ (j + k)` along two index maps with finite fibres:
the weight landing on `b (P + 1) (Q + 1)` is the product of the fibre sums of `2 ^ j` over `P` and
of `2 ^ k` over `Q`. -/
private theorem hasSum_fiber {α β : ℕ → Type} [∀ P, Fintype (α P)] [∀ Q, Fintype (β Q)]
    (e₁ : ℕ × ℕ ≃ Σ P, α P) (e₂ : ℕ × ℕ ≃ Σ Q, β Q) (f₁ f₂ : ℕ → ℕ → ℕ)
    (hf₁ : ∀ j n, (e₁ (j, n)).1 + 1 = f₁ j n) (hf₂ : ∀ k m, (e₂ (k, m)).1 + 1 = f₂ k m)
    (b : ℕ → ℕ → ℂ)
    (hF : Summable fun x : (ℕ × ℕ) × (ℕ × ℕ) =>
      (2 : ℂ) ^ (x.1.1 + x.1.2) * b (f₁ x.1.1 x.2.1) (f₂ x.1.2 x.2.2)) :
    HasSum (fun y : ℕ × ℕ => (∑ a : α y.1, (2 : ℂ) ^ (e₁.symm ⟨y.1, a⟩).1)
        * (∑ c : β y.2, (2 : ℂ) ^ (e₂.symm ⟨y.2, c⟩).1) * b (y.1 + 1) (y.2 + 1))
      (∑' x : (ℕ × ℕ) × (ℕ × ℕ),
        (2 : ℂ) ^ (x.1.1 + x.1.2) * b (f₁ x.1.1 x.2.1) (f₂ x.1.2 x.2.2)) := by
  let φ : (Σ y : ℕ × ℕ, α y.1 × β y.2) ≃ (ℕ × ℕ) × (ℕ × ℕ) :=
    (sigmaProdEquiv α β).trans ((e₁.symm.prodCongr e₂.symm).trans
      (Equiv.prodProdProdComm ℕ ℕ ℕ ℕ))
  refine ((φ.hasSum_iff.mpr hF.hasSum).sigma fun y => hasSum_fintype _).congr_fun fun y => ?_
  have key₁ (a : α y.1) : f₁ (e₁.symm ⟨y.1, a⟩).1 (e₁.symm ⟨y.1, a⟩).2 = y.1 + 1 := by
    rw [← hf₁, Prod.mk.eta, Equiv.apply_symm_apply]
  have key₂ (c : β y.2) : f₂ (e₂.symm ⟨y.2, c⟩).1 (e₂.symm ⟨y.2, c⟩).2 = y.2 + 1 := by
    rw [← hf₂, Prod.mk.eta, Equiv.apply_symm_apply]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  change _ = (2 : ℂ) ^ ((e₁.symm ⟨y.1, a⟩).1 + (e₂.symm ⟨y.2, c⟩).1)
      * b (f₁ (e₁.symm ⟨y.1, a⟩).1 (e₁.symm ⟨y.1, a⟩).2)
        (f₂ (e₂.symm ⟨y.2, c⟩).1 (e₂.symm ⟨y.2, c⟩).2)
  rw [key₁, key₂, pow_add]

private theorem sum_fin_two_pow (ν : ℕ) : ∑ i : Fin ν, (2 : ℂ) ^ (i : ℕ) = 2 ^ ν - 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => (2 : ℂ) ^ i) ν]
  have h := geom_sum_mul (2 : ℂ) ν
  rwa [show (2 : ℂ) - 1 = 1 by norm_num, mul_one] at h

end tsum_twoAdic_double_multisection

open tsum_twoAdic_double_multisection in
/-- **Double 2-adic multisection of a double series.** Let $(b_{p,q})_{p, q \ge 1}$ be a double
sequence of complex numbers such that each of the four families
$2^{j+k} b_{(2n-1) 2^j, (2m-1) 2^k}$, $2^{j+k} b_{(2n) 2^j, (2m) 2^k}$,
$2^{j+k} b_{(2n) 2^j, (2m-1) 2^k}$ and $2^{j+k} b_{(2n-1) 2^j, (2m) 2^k}$, indexed by the
quadruples $(j, k, n, m)$ with $j, k \ge 0$ and $n, m \ge 1$, is summable. Then
$$\sum_{p, q \ge 1} b_{p,q} = \sum_{j, k \ge 0,\ n, m \ge 1} 2^{j+k} \bigl(
b_{(2n-1) 2^j, (2m-1) 2^k} + b_{(2n) 2^j, (2m) 2^k} -
b_{(2n) 2^j, (2m-1) 2^k} - b_{(2n-1) 2^j, (2m) 2^k} \bigr),$$
where both sides are unconditional sums, over the pairs $(p, q)$ and the quadruples
$(j, k, n, m)$ respectively.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Proposition 15, sum version (`jis-2024-24.5.5-prop-15`). -/
public theorem tsum_twoAdic_double_multisection (b : ℕ → ℕ → ℂ)
    (h₁ : Summable fun x : (ℕ × ℕ) × (ℕ × ℕ) =>
      (2 : ℂ) ^ (x.1.1 + x.1.2) * b ((2 * x.2.1 + 1) * 2 ^ x.1.1) ((2 * x.2.2 + 1) * 2 ^ x.1.2))
    (h₂ : Summable fun x : (ℕ × ℕ) × (ℕ × ℕ) =>
      (2 : ℂ) ^ (x.1.1 + x.1.2) * b ((2 * x.2.1 + 2) * 2 ^ x.1.1) ((2 * x.2.2 + 2) * 2 ^ x.1.2))
    (h₃ : Summable fun x : (ℕ × ℕ) × (ℕ × ℕ) =>
      (2 : ℂ) ^ (x.1.1 + x.1.2) * b ((2 * x.2.1 + 2) * 2 ^ x.1.1) ((2 * x.2.2 + 1) * 2 ^ x.1.2))
    (h₄ : Summable fun x : (ℕ × ℕ) × (ℕ × ℕ) =>
      (2 : ℂ) ^ (x.1.1 + x.1.2) * b ((2 * x.2.1 + 1) * 2 ^ x.1.1) ((2 * x.2.2 + 2) * 2 ^ x.1.2)) :
    ∑' p : ℕ × ℕ, b (p.1 + 1) (p.2 + 1)
      = ∑' x : (ℕ × ℕ) × (ℕ × ℕ), (2 : ℂ) ^ (x.1.1 + x.1.2)
          * (b ((2 * x.2.1 + 1) * 2 ^ x.1.1) ((2 * x.2.2 + 1) * 2 ^ x.1.2)
            + b ((2 * x.2.1 + 2) * 2 ^ x.1.1) ((2 * x.2.2 + 2) * 2 ^ x.1.2)
            - b ((2 * x.2.1 + 2) * 2 ^ x.1.1) ((2 * x.2.2 + 1) * 2 ^ x.1.2)
            - b ((2 * x.2.1 + 1) * 2 ^ x.1.1) ((2 * x.2.2 + 2) * 2 ^ x.1.2)) := by
  have hodd (j n : ℕ) : (oddEquiv (j, n)).1 + 1 = (2 * n + 1) * 2 ^ j :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by positivity))
  have heven (j n : ℕ) : (evenEquiv (j, n)).1 + 1 = (2 * n + 2) * 2 ^ j :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by positivity))
  have wodd (P : ℕ) :
      ∑ a : Unit, (2 : ℂ) ^ (oddEquiv.symm ⟨P, a⟩).1 = 2 ^ padicValNat 2 (P + 1) := by
    simp [oddEquiv]
  have weven (P : ℕ) : ∑ a : Fin (padicValNat 2 (P + 1)), (2 : ℂ) ^ (evenEquiv.symm ⟨P, a⟩).1
      = 2 ^ padicValNat 2 (P + 1) - 1 :=
    sum_fin_two_pow _
  have H₁ := hasSum_fiber oddEquiv oddEquiv _ _ hodd hodd b h₁
  have H₂ := hasSum_fiber evenEquiv evenEquiv _ _ heven heven b h₂
  have H₃ := hasSum_fiber evenEquiv oddEquiv _ _ heven hodd b h₃
  have H₄ := hasSum_fiber oddEquiv evenEquiv _ _ hodd heven b h₄
  refine ((((H₁.add H₂).sub H₃).sub H₄).congr_fun fun y => ?_).tsum_eq.trans ?_
  · simp only [wodd, weven]
    ring
  · rw [← h₁.tsum_add h₂, ← (h₁.add h₂).tsum_sub h₃, ← ((h₁.add h₂).sub h₃).tsum_sub h₄]
    exact tsum_congr fun x => by ring

/-- Regroup a weighted family along an index map with finite fibres. The resulting `HasSum`
records summability of the outer series as well as its sum. -/
private theorem hasSum_multisection_fibers {α : ℕ → Type} [∀ m, Fintype (α m)]
    (e : ℕ × ℕ ≃ Σ m, α m) (f : ℕ → ℕ → ℕ)
    (hf : ∀ j n, (e (j, n)).1 + 1 = f j n) (w b : ℕ → ℂ)
    (hs : Summable fun x : ℕ × ℕ => w x.1 * b (f x.1 x.2)) :
    HasSum (fun m => (∑ a : α m, w (e.symm ⟨m, a⟩).1) * b (m + 1))
      (∑' x : ℕ × ℕ, w x.1 * b (f x.1 x.2)) := by
  have hreindexed := e.symm.hasSum_iff.mpr hs.hasSum
  refine (hreindexed.sigma fun m => hasSum_fintype _).congr_fun fun m => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  change _ = w (e.symm ⟨m, a⟩).1 * b (f (e.symm ⟨m, a⟩).1 (e.symm ⟨m, a⟩).2)
  rw [← hf, Prod.mk.eta, Equiv.apply_symm_apply]

/-- The sum of the odd and signed even weights is one, including at `q = 1`. -/
private theorem parametric_multisection_weight (q : ℂ) (v : ℕ) :
    q ^ v - (∑ j : Fin v, q ^ (j : ℕ) * (q - 1)) = 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun j => q ^ j * (q - 1)) v, ← Finset.sum_mul,
    geom_sum_mul, sub_sub_cancel]

open tsum_twoAdic_double_multisection in
/-- **Parametric two-adic multisection.** Let $q \in \mathbb{C}$ and let $b : \mathbb{N} \to
\mathbb{C}$ be a sequence (its value at $0$ is not used). Suppose that the families
$(q^j b_{(2n-1) 2^j})$ and $(q^j (q - 1) b_{2n \cdot 2^j})$, indexed by the pairs $(j, n)$ of
natural numbers with $n \ge 1$, are summable. Then
$$\sum_{j \ge 0,\ n \ge 1} \left(q^j b_{(2n-1) 2^j} - q^j (q - 1) b_{2n \cdot 2^j}\right)
= \sum_{m \ge 1} b_m.$$

The two summability hypotheses imply that $(b_m)_{m \ge 1}$ is summable.

Source: Christophe Vignat and Michael Milgram, *Curious Multisection Identities by
Index Factorization*, Journal of Integer Sequences 27 (2024), Article 24.5.5,
Proposition 1, series version (`jis-2024-24.5.5-prop-1`). -/
public theorem tsum_twoAdic_parametric_multisection (q : ℂ) (b : ℕ → ℂ)
    (hodd : Summable fun x : ℕ × ℕ => q ^ x.1 * b ((2 * x.2 + 1) * 2 ^ x.1))
    (heven : Summable fun x : ℕ × ℕ => q ^ x.1 * (q - 1) * b ((2 * x.2 + 2) * 2 ^ x.1)) :
    ∑' x : ℕ × ℕ, (q ^ x.1 * b ((2 * x.2 + 1) * 2 ^ x.1)
        - q ^ x.1 * (q - 1) * b ((2 * x.2 + 2) * 2 ^ x.1))
      = ∑' m : ℕ, b (m + 1) := by
  have hoddIndex (j n : ℕ) : (oddEquiv (j, n)).1 + 1 = (2 * n + 1) * 2 ^ j :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by positivity))
  have hevenIndex (j n : ℕ) : (evenEquiv (j, n)).1 + 1 = (2 * n + 2) * 2 ^ j :=
    Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (by positivity))
  have hoddGrouped := hasSum_multisection_fibers oddEquiv _ hoddIndex (q ^ ·) b hodd
  have hevenGrouped :=
    hasSum_multisection_fibers evenEquiv _ hevenIndex (fun j => q ^ j * (q - 1)) b heven
  rw [hodd.tsum_sub heven]
  refine ((hoddGrouped.sub hevenGrouped).congr_fun fun m => ?_).tsum_eq.symm
  simp only [Fintype.sum_unique]
  change b (m + 1) = q ^ padicValNat 2 (m + 1) * b (m + 1) -
    (∑ j : Fin (padicValNat 2 (m + 1)), q ^ (j : ℕ) * (q - 1)) * b (m + 1)
  rw [← sub_mul, parametric_multisection_weight, one_mul]

end MetaMathlibExt
