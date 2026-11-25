/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Order.Filter.Cofinite
public import Mathlib.Order.Filter.Ultrafilter.Defs
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Order.Filter.Ultrafilter.Basic

/-!
# Bergman's question on homomorphic images of countable ultraproducts

Following Corson's counterexample, we refute Bergman's question 21.12 in the Kourovka Notebook.
The direct sum of cyclic groups of orders `2 ^ (n + 1)` satisfies the local condition for every
ultrafilter. Finite support prevents it from being an image of a nonprincipal ultraproduct.

Source: S. M. Corson, *On homomorphic images of ultraproducts*, Section 2,
https://arxiv.org/abs/2503.09228.
-/

@[expose] public section

namespace MathlibExt.GroupTheory.UltraproductImageKourovka21Problem12Wanted

/-- **Groups locally an image of the ultrapower $\mathbb{Z}^{\mathbb{N}}/U$.** Let $U$ be an
ultrafilter on $\mathbb{N}$ and $B$ a group. Then $B$ is locally an image of the ultrapower
$\mathbb{Z}^{\mathbb{N}}/U$ when every element $b \in B$ lies in a subgroup $H$ of $B$ that is a
homomorphic image of $\mathbb{Z}^{\mathbb{N}}/U$: there is a surjective homomorphism $\psi$ from
the additive group $\mathbb{Z}^{\mathbb{N}}$ of integer sequences onto $H$ such that $\psi(f) = 1$
for every sequence $f$ with $f_i = 0$ for $U$-almost every $i$. -/
def IsLocallyUltrapowerImage (U : Ultrafilter ℕ) (B : Type) [Group B] : Prop :=
  ∀ b : B, ∃ (H : Subgroup B) (ψ : Multiplicative (ℕ → ℤ) →* H), b ∈ H ∧ Function.Surjective ψ ∧
    ∀ f : ℕ → ℤ, (∀ᶠ i in (U : Filter ℕ), f i = 0) → ψ (Multiplicative.ofAdd f) = 1

/-- **Bergman's question on images of countable ultraproducts (Kourovka 21.12).** There is a
nonprincipal ultrafilter $U$ on $\mathbb{N}$ such that every group $B$ that is locally an image of
the ultrapower $\mathbb{Z}^{\mathbb{N}}/U$ (every element of $B$ lies in a subgroup of $B$ that is
a homomorphic image of $\mathbb{Z}^{\mathbb{N}}/U$) is a homomorphic image of an ultraproduct
$(\prod_{i \in \mathbb{N}} G_i)/U$: there are groups $G_i$, $i \in \mathbb{N}$, and a surjective
homomorphism $\varphi \colon \prod_i G_i \to B$ such that $\varphi(f) = 1$ for every family $f$
with $f_i = 1$ for $U$-almost every $i$.

The question is posed for a fixed nonprincipal $U$; it is stated here for some $U$, so that its
refutation covers every $U$. -/
def locallyUltrapowerImageIsUltraproductImage : Prop :=
  ∃ U : Ultrafilter ℕ, (U : Filter ℕ) ≤ Filter.cofinite ∧
    ∀ (B : Type) [Group B], IsLocallyUltrapowerImage U B →
      ∃ (G : ℕ → Type) (_ : ∀ i, Group (G i)) (φ : (∀ i, G i) →* B), Function.Surjective φ ∧
        ∀ f : ∀ i, G i, (∀ᶠ i in (U : Filter ℕ), f i = 1) → φ f = 1

open Filter
open scoped DirectSum

private abbrev Cyclic (n : ℕ) := ZMod (2 ^ (n + 1))
private abbrev CyclicSum := ⨁ n, Cyclic n

-- On a finite cyclic subgroup the ultrafilter selects one value of each sequence of powers.
private theorem locally_of_torsion (U : Ultrafilter ℕ) {B : Type} [Group B]
    (hB : ∀ b : B, IsOfFinOrder b) : IsLocallyUltrapowerImage U B := by
  intro b
  let H := Subgroup.zpowers b
  let : Finite H := Finite.of_equiv _ (finEquivZPowers (hB b))
  let p (n : ℤ) : H := ⟨b ^ n, Subgroup.zpow_mem_zpowers b n⟩
  have select (f : ℕ → ℤ) : ∃ a : H, ∀ᶠ i in U, p (f i) = a :=
    Ultrafilter.eventually_exists_iff.mp (.of_forall fun i => ⟨p (f i), rfl⟩)
  choose value hvalue using select
  have eq_of_eventually (f : ℕ → ℤ) (a : H) (ha : ∀ᶠ i in U, p (f i) = a) : value f = a := by
    obtain ⟨i, hi, hi'⟩ := ((hvalue f).and ha).exists
    exact hi.symm.trans hi'
  let ψ : Multiplicative (ℕ → ℤ) →* H :=
    { toFun := fun f => value f.toAdd
      map_one' := eq_of_eventually _ _ (.of_forall fun i => Subtype.ext (zpow_zero b))
      map_mul' := fun f g => by
        apply eq_of_eventually
        filter_upwards [hvalue f.toAdd, hvalue g.toAdd] with i hf hg
        rw [← hf, ← hg]
        exact Subtype.ext (zpow_add b _ _) }
  refine ⟨H, ψ, Subgroup.mem_zpowers b, ?_, ?_⟩
  · rintro ⟨a, n, rfl⟩
    exact ⟨Multiplicative.ofAdd (fun _ => n), eq_of_eventually _ _ (.of_forall fun _ => rfl)⟩
  · intro f hf
    apply eq_of_eventually
    filter_upwards [hf] with i hi
    change p (f i) = 1
    rw [hi]
    exact Subtype.ext (zpow_zero b)

private theorem locally_cyclicSum (U : Ultrafilter ℕ) :
    IsLocallyUltrapowerImage U (Multiplicative CyclicSum) := by
  apply locally_of_torsion
  intro b
  change IsOfFinAddOrder b.toAdd
  induction b.toAdd using DirectSum.induction_on with
  | zero => exact IsOfFinAddOrder.zero
  | of i x => exact (DirectSum.of Cyclic i).isOfFinAddOrder (isOfFinAddOrder_of_finite x)
  | add _ _ hx hy => exact hx.add hy

-- Truncate the nested word at each coordinate of the product. As the truncation depth grows,
-- each fixed equation eventually holds and therefore passes to the image.
private def nestedWord {G : Type*} [Group G] (g : ℕ → G) : ℕ → ℕ → G
  | 0, _ => 1
  | d + 1, n => g n * nestedWord g d (n + 1) ^ 2

private theorem exists_recurrence {U : Ultrafilter ℕ} (hU : (U : Filter ℕ) ≤ cofinite)
    {G : ℕ → Type} [∀ i, Group (G i)] {B : Type} [Group B]
    (φ : (∀ i, G i) →* B) (hs : Function.Surjective φ)
    (hk : ∀ f : ∀ i, G i, (∀ᶠ i in U, f i = 1) → φ f = 1) (b : ℕ → B) :
    ∃ x : ℕ → B, ∀ n, x n = b n * x (n + 1) ^ 2 := by
  choose g hg using fun n => hs (b n)
  let y (n i : ℕ) := nestedWord (fun k => g k i) (i - n) n
  refine ⟨fun n => φ (y n), fun n => ?_⟩
  have heq : ∀ᶠ i in U, y n i = g n i * y (n + 1) i ^ 2 := by
    filter_upwards [(eventually_gt_atTop n).filter_mono (hU.trans_eq Nat.cofinite_eq_atTop)]
      with i hi
    dsimp only [y]
    rw [show i - n = (i - (n + 1)) + 1 by omega, nestedWord]
  have hker := hk (y n / (g n * y (n + 1) ^ 2)) (heq.mono fun i hi => div_eq_one.mpr hi)
  simpa only [map_div, div_eq_one, map_mul, map_pow, hg] using hker

private abbrev generator (n : ℕ) : CyclicSum := DirectSum.of Cyclic n 1

-- Modulo 2^(k+1) the equation at k kills the tail and forces the kth coordinate of x₀ to be 2^k.
private theorem no_recurrence (x : ℕ → CyclicSum)
    (hx : ∀ n, x n = generator n + 2 • x (n + 1)) : False := by
  classical
  obtain ⟨k, hk⟩ := (x 0).support.exists_notMem
  have step (n : ℕ) : x n k = generator n k + 2 * x (n + 1) k := by
    simpa [two_nsmul, two_mul] using congrArg (fun z : CyclicSum => z k) (hx n)
  have expand (n : ℕ) (hn : n ≤ k) : x 0 k = 2 ^ n * x n k := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [ih (by omega), step n, DirectSum.of_eq_of_ne _ _ _ (by omega : k ≠ n)]
      simp [pow_succ, mul_assoc]
  have hzero : (2 : Cyclic k) ^ (k + 1) = 0 := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using ZMod.natCast_self (2 ^ (k + 1))
  have hval : x 0 k = 2 ^ k := by
    calc
      x 0 k = 2 ^ k * x k k := expand k le_rfl
      _ = 2 ^ k + 2 ^ (k + 1) * x (k + 1) k := by
        rw [step k, DirectSum.of_eq_same, mul_add, mul_one, pow_succ (2 : Cyclic k), mul_assoc]
      _ = 2 ^ k := by simp [hzero]
  have hnonzero : (2 : Cyclic k) ^ k ≠ 0 := by
    have hlt : 2 ^ k < 2 ^ (k + 1) := Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self k)
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      (mt (ZMod.natCast_eq_zero_iff _ _).mp (Nat.not_dvd_of_pos_of_lt (Nat.two_pow_pos k) hlt))
  exact hk (DFinsupp.mem_support_iff.mpr (hval ▸ hnonzero))

/-- **Bergman's question 21.12 has a negative answer.** For every nonprincipal ultrafilter $U$
on $\mathbb{N}$ there is a group $B$ that is locally an image of the ultrapower
$\mathbb{Z}^{\mathbb{N}}/U$ (every element of $B$ lies in a subgroup of $B$ that is a homomorphic
image of $\mathbb{Z}^{\mathbb{N}}/U$) but is not a homomorphic image of any ultraproduct
$(\prod_{i \in \mathbb{N}} G_i)/U$ of groups: for no groups $G_i$, $i \in \mathbb{N}$, is there a
surjective homomorphism $\varphi \colon \prod_i G_i \to B$ with $\varphi(f) = 1$ for every family
$f$ such that $f_i = 1$ for $U$-almost every $i$.

Corson shows that the abelian group $\bigoplus_n C_n$, with $C_n$ finite cyclic of unbounded
orders, is such a group for every nonprincipal $U$: it is not a homomorphic image of any
nonprincipal countable ultraproduct. The Kourovka Notebook marks 21.12 solved ("No, it need not").

Source: E. I. Khukhro and V. D. Mazurov (eds.), Unsolved Problems in Group
Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49 (2026), Problem 21.12 (G. M. Bergman);
resolution: S. M. Corson, On homomorphic images of ultraproducts, J. Algebra 681 (2025), 306-317,
arXiv:2503.09228, Section 2, proof of the negative answer to Question 3 (Bergman's Question 19): for
every nonprincipal ultrafilter U on ω the group ⊕ₙ Cₙ, Cₙ finite cyclic of unbounded orders, has
each element in a homomorphic image of (∏ ℤ)/U but is not a homomorphic image of any nonprincipal
ultraproduct (∏ Gᵢ)/V; Kourovka Notebook (21st issue), Problem 21.12: No, it need not,
https://arxiv.org/abs/2503.09228.
-/
theorem locallyUltrapowerImageIsUltraproductImage_refuted :
    ¬ locallyUltrapowerImageIsUltraproductImage := by
  rintro ⟨U, hU, h⟩
  obtain ⟨G, inst, φ, hs, hk⟩ := h _ (locally_cyclicSum U)
  obtain ⟨x, hx⟩ := exists_recurrence hU φ hs hk (fun n => Multiplicative.ofAdd (generator n))
  exact no_recurrence (fun n => (x n).toAdd) hx

end MathlibExt.GroupTheory.UltraproductImageKourovka21Problem12Wanted
