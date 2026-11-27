/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Quaternion.Split
public import MathlibExt.Algebra.QuadraticForm.NormForm
public import MathlibExt.NumberTheory.Padics.HilbertSymbol.OddFormula

/-!
# The ramified primes $\Delta_{a,b}$ of the quaternion algebra $H_{a,b}$

For $a, b$ in a commutative ring $R$, `ℍ[R,a,b]` is the quaternion algebra with basis
$1, i, j, ij$, $i^2 = a$, $j^2 = b$ and $ij = -ji$. For an element
$x = x_1 + x_2 i + x_3 j + x_4 ij$, the reduced trace and the reduced norm are
$\operatorname{trd}(x) = x + \bar x = 2x_1$ and
$\operatorname{nrd}(x) = x \bar x = x_1^2 - a x_2^2 - b x_3^2 + ab x_4^2$.

For $a, b \in \mathbb{Q}$, B. Poonen's $H_{a,b}$ is `ℍ[ℚ,a,b]`, and
$H_{a,b} \otimes \mathbb{Q}_p$ is `ℍ[ℚ_[p],a,b]`. A prime $p$ ramifies in $H_{a,b}$ if
$H_{a,b} \otimes \mathbb{Q}_p$ is not isomorphic to $M_2(\mathbb{Q}_p)$;
`Rat.quaternionRamifiedPrimes a b` is the set $\Delta_{a,b}$ of these primes. For
$a, b \in \mathbb{Q}^\times$, $p \in \Delta_{a,b}$ exactly when the $p$-adic Hilbert symbol
$(a, b)_p$ is $-1$ (`Rat.mem_quaternionRamifiedPrimes_iff`).
-/

set_option autoImplicit false

@[expose] public section

open scoped Quaternion

namespace QuaternionAlgebra

variable {R : Type*} [CommRing R] (a b : R)

/-- The reduced norm of $H_{a,b}$: $x \bar x = x_1^2 - a x_2^2 - b x_3^2 + ab x_4^2$ for
$x = x_1 + x_2 i + x_3 j + x_4 ij$ in `ℍ[R, a, b]`. -/
private theorem self_mul_star_eq_normForm (x : ℍ[R,a,b]) :
    x * star x = algebraMap R ℍ[R,a,b]
      (x.re ^ 2 - a * x.imI ^ 2 - b * x.imJ ^ 2 + a * b * x.imK ^ 2) := by
  ext <;> simp [QuaternionAlgebra.algebraMap_eq] <;> ring

/-- **$(ij)^2 = -ab$ in $H_{a,b}$.** In the quaternion algebra `ℍ[R,a,b]`, with $i^2 = a$,
$j^2 = b$ and $ij = -ji$, the basis element $ij$ satisfies $(ij)^2 = -ab$; this is where the
coefficient $ab$ of $x_4^2$ in the reduced norm comes from. -/
theorem i_mul_j_sq :
    ((⟨0, 1, 0, 0⟩ : ℍ[R,a,b]) * ⟨0, 0, 1, 0⟩) ^ 2 = algebraMap R ℍ[R,a,b] (-(a * b)) := by
  simp [QuaternionAlgebra.algebraMap_eq, pow_two]

/-- **Splitting of $H_{a,b}$ by the Hilbert symbol.** Let $F$ be a field with $2 \ne 0$ and let
$a, b \in F^\times$. The quaternion algebra `ℍ[F,a,b]` is isomorphic to the matrix algebra
$M_2(F)$ if and only if the Hilbert symbol $(a, b)_F$ is $1$.

The proof: if $(a, b)_F = 1$, the ternary form $z^2 - ax^2 - by^2$ has a nontrivial zero
(`hilbertSymbol.eq_one_iff_exists_ternary_eq_zero`), so the norm form is isotropic and the algebra
splits (`QuaternionAlgebra.nonempty_algEquiv_matrix_of_normForm_eq_zero`). Conversely, if
$\varphi \colon \mathbb{H} \to M_2(F)$ is an isomorphism, $\alpha = \varphi^{-1}(E_{11})$ is nonzero
and not invertible; since $\alpha \bar\alpha = \operatorname{nrd}(\alpha)$, its reduced norm is $0$,
so the norm form, and with it the ternary form
(`QuadraticForm.forall_quaternary_normForm_eq_zero_iff_forall_ternary_eq_zero`), is isotropic.

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020),
<https://www.jmilne.org/math/CourseNotes/CFT.pdf>, Chapter IV, Exercise 5.7(b), p. 144: a
quaternion algebra over a field of characteristic not two splits if and only if its norm form has
a nontrivial zero. -/
theorem nonempty_algEquiv_matrix_iff_hilbertSymbol_eq_one {F : Type} [Field F] (h2 : (2 : F) ≠ 0)
    (a b : Fˣ) :
    Nonempty (ℍ[F,(a : F),(b : F)] ≃ₐ[F] Matrix (Fin 2) (Fin 2) F) ↔
      hilbertSymbol F a b = 1 := by
  rw [hilbertSymbol.eq_one_iff_exists_ternary_eq_zero h2]
  constructor
  · rintro ⟨φ⟩
    set E : Matrix (Fin 2) (Fin 2) F := !![1, 0; 0, 0] with hE
    set α := φ.symm E with hαdef
    have hα0 : α ≠ 0 := by
      intro h
      have hE0 : E = 0 := by rw [← φ.apply_symm_apply E, ← hαdef, h, map_zero]
      have := congrFun (congrFun hE0 0) 0
      simp [hE] at this
    -- The reduced norm of `α` is `0`.
    have hn : α.re ^ 2 - (a : F) * α.imI ^ 2 - (b : F) * α.imJ ^ 2 +
        (a : F) * (b : F) * α.imK ^ 2 = 0 := by
      by_contra hn
      set n := α.re ^ 2 - (a : F) * α.imI ^ 2 - (b : F) * α.imJ ^ 2 +
        (a : F) * (b : F) * α.imK ^ 2 with hndef
      have hinv : α * (algebraMap F _ n⁻¹ * star α) = 1 := by
        rw [← mul_assoc, ← Algebra.commutes, mul_assoc, self_mul_star_eq_normForm, ← map_mul,
          inv_mul_cancel₀ hn, map_one]
      have hφ := congrArg φ hinv
      rw [map_mul, map_one, hαdef, φ.apply_symm_apply] at hφ
      have hdet := congrArg Matrix.det hφ
      rw [Matrix.det_mul, Matrix.det_one] at hdet
      simp [hE, Matrix.det_fin_two] at hdet
    -- So the ternary form is isotropic.
    have hiso := (QuadraticForm.forall_quaternary_normForm_eq_zero_iff_forall_ternary_eq_zero F
      (a : F) (b : F)).not.1 (by
        push Not
        refine ⟨α.re, α.imI, α.imJ, α.imK, hn, fun h0 h1 h2 h3 => hα0 ?_⟩
        ext <;> simp [h0, h1, h2, h3])
    push Not at hiso
    obtain ⟨z, x, y, hz, hne⟩ := hiso
    exact ⟨z, x, y, fun ⟨h1, h2, h3⟩ => hne h1 h2 h3, hz⟩
  · rintro ⟨z, x, y, hne, hz⟩
    exact QuaternionAlgebra.nonempty_algEquiv_matrix_of_normForm_eq_zero F h2 a b a.ne_zero
      b.ne_zero z x y 0 (by tauto) (by linear_combination hz)

end QuaternionAlgebra

namespace Rat

/-- **The ramified primes $\Delta_{a,b}$ of the quaternion algebra $H_{a,b}$.** For
$a, b \in \mathbb{Q}$, the set of primes $p$ such that $H_{a,b} \otimes \mathbb{Q}_p$, the
quaternion algebra `ℍ[ℚ_[p],a,b]` over $\mathbb{Q}_p$ with $i^2 = a$, $j^2 = b$ and $ij = -ji$, is
not isomorphic to the matrix algebra $M_2(\mathbb{Q}_p)$ as a $\mathbb{Q}_p$-algebra.

The source takes $a, b \in \mathbb{Q}^\times$; the definition makes sense for all $a, b$.

Source: B. Poonen, "Characterizing integers among rational numbers with a universal-existential
formula", Amer. J. Math. 131 (2009), 675–682, §2, p. 2 of the author's version with the corrections
of April 15, 2019 (<https://math.mit.edu/~poonen/papers/ae.pdf>): "Given
$a, b \in \mathbb{Q}^\times$, let $H_{a,b}$ be the quaternion algebra over $\mathbb{Q}$ generated by
$i$ and $j$ satisfying $i^2 = a$, $j^2 = b$, and $ij = -ji$. Let $\Delta_{a,b}$ be the set of
$p \in \mathcal{P}$ that ramify in $H_{a,b}$", with ramification as used in the proof of Lemma 2.1,
p. 3: "If $p \notin \Delta_{a,b}$, then $H_{a,b} \otimes \mathbb{Q}_p \simeq M_2(\mathbb{Q}_p)$". -/
def quaternionRamifiedPrimes (a b : ℚ) : Set Nat.Primes :=
  {p | haveI : Fact (p : ℕ).Prime := ⟨p.prop⟩
    IsEmpty (ℍ[ℚ_[p],(a : ℚ_[p]),(b : ℚ_[p])] ≃ₐ[ℚ_[p]] Matrix (Fin 2) (Fin 2) ℚ_[p])}

/-- **Ramification of $H_{a,b}$ is detected by the Hilbert symbol.** Let
$a, b \in \mathbb{Q}^\times$ and let $p$ be a prime. Then $p \in \Delta_{a,b}$, that is, $p$
ramifies in the quaternion algebra $H_{a,b}$, if and only if the $p$-adic Hilbert symbol of the
images of $a$ and $b$ in $\mathbb{Q}_p$ is $(a, b)_p = -1$.

This follows from `QuaternionAlgebra.nonempty_algEquiv_matrix_iff_hilbertSymbol_eq_one` over
$\mathbb{Q}_p$ and `padicHilbertSymbol.eq_one_or_neg_one`.

Source: J. S. Milne, *Class Field Theory*, version 4.03 (2020),
<https://www.jmilne.org/math/CourseNotes/CFT.pdf>, Chapter IV, Exercise 5.7(b), p. 144 (splitting
of a quaternion algebra over a field of characteristic not two exactly when its norm form has a
nontrivial zero), with the definition of $\Delta_{a,b}$ in B. Poonen, "Characterizing integers among
rational numbers with a universal-existential formula", Amer. J. Math. 131 (2009), 675–682, §2,
p. 2 of the author's version with the corrections of April 15, 2019. -/
theorem mem_quaternionRamifiedPrimes_iff (a b : ℚˣ) (p : Nat.Primes) :
    p ∈ quaternionRamifiedPrimes a b ↔
      (haveI : Fact (p : ℕ).Prime := ⟨p.prop⟩
      padicHilbertSymbol p (Units.map (Rat.castHom ℚ_[p]).toMonoidHom a)
        (Units.map (Rat.castHom ℚ_[p]).toMonoidHom b) = -1) := by
  have : Fact (p : ℕ).Prime := ⟨p.prop⟩
  have h := QuaternionAlgebra.nonempty_algEquiv_matrix_iff_hilbertSymbol_eq_one (F := ℚ_[p])
    two_ne_zero (Units.map (Rat.castHom ℚ_[p]).toMonoidHom a)
    (Units.map (Rat.castHom ℚ_[p]).toMonoidHom b)
  change IsEmpty (ℍ[ℚ_[p],((a : ℚ) : ℚ_[p]),((b : ℚ) : ℚ_[p])] ≃ₐ[ℚ_[p]]
    Matrix (Fin 2) (Fin 2) ℚ_[p]) ↔ _
  rw [← not_nonempty_iff]
  change ¬Nonempty (ℍ[ℚ_[p],((Units.map (Rat.castHom ℚ_[p]).toMonoidHom a : ℚ_[p]ˣ) : ℚ_[p]),
    ((Units.map (Rat.castHom ℚ_[p]).toMonoidHom b : ℚ_[p]ˣ) : ℚ_[p])] ≃ₐ[ℚ_[p]]
      Matrix (Fin 2) (Fin 2) ℚ_[p]) ↔ _
  rw [h]
  rcases padicHilbertSymbol.eq_one_or_neg_one (Units.map (Rat.castHom ℚ_[p]).toMonoidHom a)
    (Units.map (Rat.castHom ℚ_[p]).toMonoidHom b) with h1 | h1
  · change hilbertSymbol ℚ_[p] _ _ = 1 at h1
    simp only [padicHilbertSymbol, h1]
    decide
  · change hilbertSymbol ℚ_[p] _ _ = -1 at h1
    simp only [padicHilbertSymbol, h1]
    decide

end Rat
