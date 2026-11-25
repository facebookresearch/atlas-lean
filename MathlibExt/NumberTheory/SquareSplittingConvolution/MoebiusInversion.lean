/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.SquareSplittingConvolution
public import Mathlib.NumberTheory.ArithmeticFunction.Zeta
import Mathlib.Data.Nat.Factorization.Root
import Mathlib.Data.Nat.Squarefree

/-!
# Möbius inversion for the square-splitting convolution

In the coordinates `n = u * v ^ 2` with `u` squarefree, square-splitting convolution is
ordinary Dirichlet convolution in each variable. This identifies convolution by an inverse
of the constant-one function with the inverse of the divisor-sum operator.
-/

namespace MetaMathlibExt
namespace squareSplit_moebius_inversion

private theorem split_coords {u v : ℕ} (hu : Squarefree u) (hv : v ≠ 0) :
    squareSplitU (u * v ^ 2) = u ∧ squareSplitV (u * v ^ 2) = v := by
  have hn := mul_ne_zero hu.ne_zero (pow_ne_zero 2 hv)
  have hroot : Nat.floorRoot 2 (u * v ^ 2) = v := by
    apply Nat.eq_of_factorization_eq (Nat.floorRoot_ne_zero.mpr ⟨by decide, hn⟩) hv
    intro p
    rw [Nat.factorization_floorRoot, Finsupp.floorDiv_apply, Nat.factorization_mul hu.ne_zero
      (pow_ne_zero 2 hv), Nat.factorization_pow]
    change (u.factorization p + 2 * v.factorization p) / 2 = v.factorization p
    have := hu.natFactorization_le_one p
    omega
  have hV : squareSplitV (u * v ^ 2) = v := by
    simpa [Nat.floorRoot, hn, squareSplitV] using hroot
  have h := squareSplitU_mul_squareSplitV_sq hn
  rw [hV] at h
  exact ⟨Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (pow_ne_zero 2 hv)) h, hV⟩

/-- Regard an arithmetic function as a function in the squarefree and square-root coordinates. -/
private def inCoords (f : ArithmeticFunction ℂ) : ArithmeticFunction (ArithmeticFunction ℂ) :=
  ⟨fun u => ⟨fun v => f (u * v ^ 2), by simp⟩, by ext v; simp⟩

private theorem inCoords_one : inCoords 1 = 1 := by
  ext u v
  change (1 : ArithmeticFunction ℂ) (u * v ^ 2) = _
  by_cases hu : u = 1 <;> simp [ArithmeticFunction.one_apply, hu]

private theorem inCoords_conv (f g : ArithmeticFunction ℂ) {u : ℕ} (hu : Squarefree u) :
    inCoords (squareSplitConv f g) u = (inCoords f * inCoords g) u := by
  apply ArithmeticFunction.ext
  intro v
  obtain rfl | hv := eq_or_ne v 0
  · simp
  change squareSplitConv f g (u * v ^ 2) = _
  obtain ⟨hU, hV⟩ := split_coords hu hv
  have hinj : Set.InjOn (fun x : ℕ × ℕ => x.1 * x.2 ^ 2) ↑(u.divisors ×ˢ v.divisors) := by
    rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd h
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    obtain ⟨hc, hd⟩ := Finset.mem_product.mp hcd
    have H₁ := split_coords (hu.squarefree_of_dvd (Nat.dvd_of_mem_divisors ha))
      (Nat.pos_of_mem_divisors hb).ne'
    have H₂ := split_coords (hu.squarefree_of_dvd (Nat.dvd_of_mem_divisors hc))
      (Nat.pos_of_mem_divisors hd).ne'
    change a * b ^ 2 = c * d ^ 2 at h
    rw [h] at H₁
    exact Prod.ext (H₁.1.symm.trans H₂.1) (H₁.2.symm.trans H₂.2)
  rw [squareSplitConv_apply _ _ (mul_ne_zero hu.ne_zero (pow_ne_zero 2 hv)), squareSplitDivisors,
    hU, hV, Finset.sum_image hinj, Finset.sum_product, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a c => inCoords f a * inCoords g c)]
  let ev : ArithmeticFunction ℂ →+ ℂ :=
    ⟨⟨fun h => h v, rfl⟩, fun _ _ => rfl⟩
  change _ = ev (∑ i ∈ u.divisors, inCoords f i * inCoords g (u / i))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  change _ = (inCoords f a * inCoords g (u / a)) v
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun b d => inCoords f a b * inCoords g (u / a) d)]
  apply Finset.sum_congr rfl
  intro b hb
  change f (a * b ^ 2) * g (u * v ^ 2 / (a * b ^ 2)) =
    f (a * b ^ 2) * g (u / a * (v / b) ^ 2)
  have hbv := Nat.dvd_of_mem_divisors hb
  rw [← Nat.div_mul_div_comm (Nat.dvd_of_mem_divisors ha) (pow_dvd_pow_of_dvd hbv 2)]
  simp only [sq, Nat.div_mul_div_comm hbv hbv]

-- A divisor of a squarefree first coordinate is again squarefree.
private theorem mul_congr_squarefree
    {a b c d : ArithmeticFunction (ArithmeticFunction ℂ)}
    (hac : ∀ u, Squarefree u → a u = c u) (hbd : ∀ u, Squarefree u → b u = d u)
    {u : ℕ} (hu : Squarefree u) : (a * b) u = (c * d) u := by
  simp only [ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  rintro ⟨i, j⟩ hij
  obtain ⟨rfl, _⟩ := Nat.mem_divisorsAntidiagonal.mp hij
  rw [hac i hu.of_mul_left, hbd j hu.of_mul_right]

private theorem cancel_conv (a b f : ArithmeticFunction ℂ)
    (hab : ∀ u, Squarefree u →
      (inCoords a * inCoords b) u = (1 : ArithmeticFunction (ArithmeticFunction ℂ)) u) :
    squareSplitConv a (squareSplitConv b f) = f := by
  apply ArithmeticFunction.ext
  intro n
  obtain ⟨v, u, rfl, hu⟩ := exists_sq_mul_squarefree n
  rw [mul_comm (v ^ 2)]
  change inCoords (squareSplitConv a (squareSplitConv b f)) u v = inCoords f u v
  apply DFunLike.congr_fun _ v
  calc
    _ = (inCoords a * inCoords (squareSplitConv b f)) u := inCoords_conv _ _ hu
    _ = (inCoords a * (inCoords b * inCoords f)) u :=
      mul_congr_squarefree (fun _ _ => rfl) (fun _ h => inCoords_conv b f h) hu
    _ = ((inCoords a * inCoords b) * inCoords f) u :=
      DFunLike.congr_fun (mul_assoc (inCoords a) (inCoords b) (inCoords f)).symm u
    _ = (1 * inCoords f) u := mul_congr_squarefree hab (fun _ _ => rfl) hu
    _ = _ := DFunLike.congr_fun (one_mul (inCoords f)) u

end squareSplit_moebius_inversion

open squareSplit_moebius_inversion

/-- **Möbius inversion for the square-splitting convolution.** Let $\star$ be the
square-splitting convolution, $\mathbf{1}$ the constant function $1$ on the positive integers,
$\varepsilon$ the identity element ($\varepsilon(1) = 1$ and $\varepsilon(n) = 0$ for $n \ne 1$),
and let $\mu_\star$ be any complex-valued arithmetic function with
$\mathbf{1} \star \mu_\star = \varepsilon$. Then for all complex-valued arithmetic functions $f$
and $F$, $F = \mathbf{1} \star f$ if and only if $f = \mu_\star \star F$; that is,
$F(n) = \sum_{d \in A(n)} f(d)$ for every $n \ge 1$ if and only if
$f(n) = \sum_{d \in A(n)} \mu_\star(d)\,F(n/d)$ for every $n \ge 1$, where $A(n)$ is the set of
square-splitting divisors of $n$.

Source: Champak Talukdar and Helen K. Saikia, *A Square-Splitting
A-Convolution of Narkiewicz Type*, INTEGERS 26 (2026), Article A56, Theorem 4
(`integers-2026-A56-thm-4`). -/
public theorem squareSplit_moebius_inversion (m : ArithmeticFunction ℂ)
    (hm : squareSplitConv (ArithmeticFunction.zeta : ArithmeticFunction ℂ) m = 1)
    (f F : ArithmeticFunction ℂ) :
    F = squareSplitConv (ArithmeticFunction.zeta : ArithmeticFunction ℂ) f ↔
      f = squareSplitConv m F := by
  have h u (hu : Squarefree u) :
      (inCoords (ArithmeticFunction.zeta : ArithmeticFunction ℂ) * inCoords m) u =
        (1 : ArithmeticFunction (ArithmeticFunction ℂ)) u := by
    rw [← inCoords_conv _ _ hu, hm, inCoords_one]
  constructor
  · rintro rfl
    apply (cancel_conv m _ f ?_).symm
    intro u hu
    rw [mul_comm (inCoords m)]
    exact h u hu
  · rintro rfl
    exact (cancel_conv _ _ _ h).symm

end MetaMathlibExt
