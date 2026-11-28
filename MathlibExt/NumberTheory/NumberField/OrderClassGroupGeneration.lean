/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.ClassGroup.Basic
public import MathlibExt.NumberTheory.NumberField.OrderInvertibleIdeals
import Mathlib.Tactic.LinearCombination

/-!
# Generation of the class group of a quadratic order by primes of prime norm

Let `O` be an order of a number field `K` (`NumberField.IsOrder K O`). Mathlib's `ClassGroup O` is
the group of invertible fractional ideals of `O` modulo the principal ones: the class group
`Cl(O)` of K. Conrad, *The conductor ideal of an order*, §5 (p. 13), and the group `cl(O)` of
A. V. Sutherland, *18.783 Elliptic Curves*, Fall 2025, Lecture 17, Corollary 17.11 (p. 5). We
prove (row M3 of the decomposition of the irreducibility of the Hilbert class polynomial):

* `NumberField.IsOrder.exists_eq_spanSingleton_mul_of_ne_bot`: for every nonzero ideal `𝔫` of
  `O`, every invertible fractional ideal of `O` is `x𝔟` with `x ∈ Kˣ` and `𝔟` an ideal of `O`
  coprime to `𝔫` (Conrad, Theorem 5.2(1));
* `NumberField.IsOrder.natCard_quotient_eq_or_eq_span_of_finrank_eq_two`: in a quadratic field, a
  nonzero prime `𝔭` of `O` contains a rational prime `p`, and `#(O/𝔭) = p` or `𝔭 = pO`;
* `NumberField.IsOrder.exists_eq_spanSingleton_mul_prod_of_finrank_eq_two`: in a quadratic field,
  for every `M ≥ 1`, every invertible fractional ideal of `O` is `x𝔭₁⋯𝔭ᵣ` with `x ∈ Kˣ` and
  invertible primes `𝔭ᵢ` of prime norm not dividing `M`, coprime to the conductor;
* `NumberField.IsOrder.closure_classGroup_mk_eq_top`: hence `ClassGroup O` is generated, already
  as a monoid, by the classes of the invertible primes of prime norm not dividing `M`.
-/

@[expose] public section

set_option autoImplicit false

open scoped nonZeroDivisors

namespace NumberField.IsOrder

variable {K : Type*} [Field K] [NumberField K] {O : Subalgebra ℤ K}

/-- The conductor of an order contains a nonzero element of the order. -/
private theorem exists_ne_zero_mem_conductor (hO : NumberField.IsOrder K O) :
    ∃ z : O, z ≠ 0 ∧ z ∈ ((O.comap (integralClosure ℤ K).val).conductorIdeal).comap
      (Subalgebra.inclusion hO.le_integralClosure) := by
  have : Module.Finite ℤ (integralClosure ℤ K) :=
    inferInstanceAs (Module.Finite ℤ (NumberField.RingOfIntegers K))
  have := hO.isLocalization
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := integralClosure ℤ K)
  classical
  obtain ⟨⟨b, hbM⟩, hb⟩ := IsLocalization.exist_integer_multiples_of_finset
    (Algebra.algebraMapSubmonoid O ℤ⁰) (s.image fun x : integralClosure ℤ K => (x : K))
  obtain ⟨z, hz, rfl⟩ := hbM
  refine ⟨algebraMap ℤ O z, ?_, ?_⟩
  · intro h
    have h' : ((algebraMap ℤ O z : O) : K) = 0 := by rw [h]; rfl
    rw [eq_intCast] at h'
    push_cast at h'
    exact nonZeroDivisors.ne_zero hz (by exact_mod_cast h')
  · rw [Ideal.mem_comap, Subalgebra.mem_conductorIdeal]
    intro t
    rw [Subalgebra.mem_comap]
    have ht : t ∈ Submodule.span ℤ (s : Set (integralClosure ℤ K)) := by
      rw [hs]; exact Submodule.mem_top
    induction ht using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨y, hy⟩ := hb (x : K) (Finset.mem_image_of_mem _ hx)
      have hy' : ((y : O) : K) = ((algebraMap ℤ O z : O) : K) * (x : K) := by
        rw [Algebra.smul_def] at hy
        exact hy
      change ((algebraMap ℤ O z : O) : K) * (x : K) ∈ O
      rw [← hy']
      exact y.2
    | zero =>
      change ((algebraMap ℤ O z : O) : K) * 0 ∈ O
      rw [mul_zero]
      exact O.zero_mem
    | add x y _ _ hx hy =>
      change ((algebraMap ℤ O z : O) : K) * ((x : K) + (y : K)) ∈ O
      rw [mul_add]
      exact O.add_mem hx hy
    | smul a x _ hx =>
      change ((algebraMap ℤ O z : O) : K) * (a • (x : K)) ∈ O
      rw [mul_smul_comm]
      exact Subalgebra.smul_mem O hx a

/-- **Every class of an order contains an ideal coprime to a given ideal.** Let $O$ be an order
in a number field $K$ (`NumberField.IsOrder`), let $\mathfrak{n} \neq 0$ be an ideal of $O$, and
let $I$ be an invertible fractional ideal of $O$ (a unit of `FractionalIdeal O⁰ K`). Then there
are $x \in K$, $x \neq 0$, and an ideal $\mathfrak{b}$ of $O$ with
$\mathfrak{b} + \mathfrak{n} = O$ and $I = x\mathfrak{b}$.

This is K. Conrad, *The conductor ideal of an order*, Theorem 5.2(1) (p. 14): "For each nonzero
ideal n in O, every ideal class in Cl(O) has a representative that is an ideal in O and is
relatively prime to n." The proof is Conrad's: with $\mathfrak{a}$ an integral ideal in the class
of $I^{-1}$ and $\mathfrak{p}_1, \dots, \mathfrak{p}_r$ the maximal ideals containing
$\mathfrak{n}$, take $x \in \mathfrak{a}$ outside every $\mathfrak{p}_i\mathfrak{a}$ and
$\mathfrak{b} = x\mathfrak{a}^{-1}$; Conrad's Chinese remainder step is replaced by an induction
on $r$. The instance `IsFractionRing O K` (which follows from `hO`,
`NumberField.IsOrder.isFractionRing`) is assumed so that $x\mathfrak{b}$ can be written with
`FractionalIdeal.spanSingleton`. -/
theorem exists_eq_spanSingleton_mul_of_ne_bot [IsFractionRing O K] (hO : NumberField.IsOrder K O)
    (I : (FractionalIdeal O⁰ K)ˣ) {n : Ideal O} (hn : n ≠ ⊥) :
    ∃ (b : Ideal O) (x : K), x ≠ 0 ∧ b ⊔ n = ⊤ ∧
      (I : FractionalIdeal O⁰ K) = FractionalIdeal.spanSingleton O⁰ x * b := by
  classical
  obtain ⟨d, a, hd, ha⟩ := FractionalIdeal.exists_eq_spanSingleton_mul (↑I⁻¹ : FractionalIdeal O⁰ K)
  set D : K := algebraMap O K d with hDdef
  have hD : D ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).mpr hd
  set X : FractionalIdeal O⁰ K := ↑I * FractionalIdeal.spanSingleton O⁰ D⁻¹ with hX
  have haX : (a : FractionalIdeal O⁰ K) * X = 1 := by
    have h1 : (↑I : FractionalIdeal O⁰ K) * ↑I⁻¹ = 1 := Units.mul_inv I
    rw [ha] at h1
    rw [← h1, hX]
    ring
  -- the maximal ideals containing `n` form a finite set
  have hfin : {q : Ideal O | q.IsMaximal ∧ n ≤ q}.Finite := by
    have := hO.finite_quotient hn
    have key : ∀ q : Ideal O, n ≤ q → ∀ x : O,
        x ∈ q ↔ Ideal.Quotient.mk n x ∈ Ideal.Quotient.mk n '' (q : Set O) := by
      intro q hq x
      refine ⟨fun hx => ⟨x, hx, rfl⟩, ?_⟩
      rintro ⟨y, hy, hxy⟩
      have hyx : y - x ∈ n := Ideal.Quotient.eq.mp hxy
      have := q.sub_mem hy (hq hyx)
      rwa [sub_sub_cancel] at this
    refine Set.Finite.of_finite_image
      (f := fun q : Ideal O => Ideal.Quotient.mk n '' (q : Set O)) (Set.toFinite _) ?_
    intro q₁ hq₁ q₂ hq₂ h
    ext x
    rw [key q₁ hq₁.2, key q₂ hq₂.2]
    exact Iff.of_eq (congrArg (fun S => Ideal.Quotient.mk n x ∈ S) h)
  -- `q * a` is strictly smaller than `a` for maximal `q`
  have hau : ∀ q : Ideal O, q.IsMaximal → q * a < a := by
    intro q hq
    refine lt_of_le_of_ne Ideal.mul_le_right fun h => hq.ne_top ?_
    have h' : (q : FractionalIdeal O⁰ K) * a = a := by rw [← FractionalIdeal.coeIdeal_mul, h]
    have h1 : (q : FractionalIdeal O⁰ K) = 1 :=
      calc (q : FractionalIdeal O⁰ K) = q * (a * X) := by rw [haX, mul_one]
        _ = (q * a) * X := by ring
        _ = 1 := by rw [h', haX]
    rw [← Ideal.one_eq_top]
    exact FractionalIdeal.coeIdeal_eq_one.mp h1
  -- choice of `α ∈ a` outside every `q * a`
  have hB : ∀ T : Finset (Ideal O), (∀ q ∈ T, q.IsMaximal) →
      ∃ α ∈ a, α ≠ 0 ∧ ∀ q ∈ T, α ∉ q * a := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
      intro _
      have ha0 : a ≠ ⊥ := by
        rintro rfl
        rw [FractionalIdeal.coeIdeal_bot, zero_mul] at haX
        exact zero_ne_one haX
      obtain ⟨α, hα, hα0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ha0
      exact ⟨α, hα, hα0, by simp⟩
    | insert q₀ T hq₀ ih =>
      intro hT
      obtain ⟨α, hαa, hα0, hαT⟩ := ih fun q hq => hT q (Finset.mem_insert_of_mem hq)
      have hq₀max : q₀.IsMaximal := hT q₀ (Finset.mem_insert_self _ _)
      by_cases hα₀ : α ∈ q₀ * a
      · obtain ⟨β, hβa, hβ⟩ := IsConcreteLE.exists_of_lt (hau q₀ hq₀max)
        have hinf : ¬ T.inf id ≤ q₀ := by
          intro h
          obtain ⟨q, hq, hle⟩ := (hq₀max.isPrime.inf_le').mp h
          have := (hT q (Finset.mem_insert_of_mem hq)).eq_of_le hq₀max.ne_top hle
          exact hq₀ (this ▸ hq)
        obtain ⟨e, he, heq₀⟩ := IsConcreteLE.not_le_iff_exists.mp hinf
        have hβe : β * e ∉ q₀ * a := by
          intro h
          obtain ⟨y, i, hi, hyi⟩ := hq₀max.exists_inv heq₀
          apply hβ
          have hβ' : β = y * (β * e) + i * β := by linear_combination (-β) * hyi
          rw [hβ']
          exact add_mem (Ideal.mul_mem_left _ y h) (Ideal.mul_mem_mul hi hβa)
        refine ⟨α + β * e, add_mem hαa (Ideal.mul_mem_right _ _ hβa), ?_, ?_⟩
        · intro h0
          apply hβe
          have : β * e = -α := by linear_combination h0
          rw [this]
          exact neg_mem hα₀
        · intro q hq h
          rcases Finset.mem_insert.mp hq with rfl | hq
          · apply hβe
            have := sub_mem h hα₀
            rwa [add_sub_cancel_left] at this
          · apply hαT q hq
            have hβe' : β * e ∈ q * a := by
              have : e * β ∈ q * a := Ideal.mul_mem_mul (Finset.inf_le (f := id) hq he) hβa
              rwa [mul_comm e β] at this
            have := sub_mem h hβe'
            rwa [add_sub_cancel_right] at this
      · refine ⟨α, hαa, hα0, fun q hq => ?_⟩
        rcases Finset.mem_insert.mp hq with rfl | hq
        · exact hα₀
        · exact hαT q hq
  obtain ⟨α, hαa, hα0, hαT⟩ := hB hfin.toFinset fun q hq => ((hfin.mem_toFinset).mp hq).1
  set α' : K := algebraMap O K α with hα'def
  have hα' : α' ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O K)).mpr hα0
  have hαle : FractionalIdeal.spanSingleton O⁰ α' ≤ (a : FractionalIdeal O⁰ K) :=
    FractionalIdeal.spanSingleton_le_iff_mem.mpr
      ((FractionalIdeal.mem_coeIdeal _).mpr ⟨α, hαa, rfl⟩)
  have hle1 : FractionalIdeal.spanSingleton O⁰ α' * X ≤ 1 :=
    calc FractionalIdeal.spanSingleton O⁰ α' * X ≤ (a : FractionalIdeal O⁰ K) * X := by
          gcongr
      _ = 1 := haX
  obtain ⟨b, hb⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hle1
  have hba : b * a = Ideal.span {α} := by
    apply FractionalIdeal.coeIdeal_injective (K := K)
    dsimp only
    rw [FractionalIdeal.coeIdeal_mul, hb, FractionalIdeal.coeIdeal_span_singleton]
    calc FractionalIdeal.spanSingleton O⁰ α' * X * a
        = FractionalIdeal.spanSingleton O⁰ α' * (a * X) := by ring
      _ = FractionalIdeal.spanSingleton O⁰ α' := by rw [haX, mul_one]
  have hbn : b ⊔ n = ⊤ := by
    by_contra h
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ h
    have hmT : m ∈ hfin.toFinset := hfin.mem_toFinset.mpr ⟨hm, le_sup_right.trans hle⟩
    apply hαT m hmT
    have : Ideal.span {α} ≤ m * a := hba ▸ Ideal.mul_mono_left (le_sup_left.trans hle)
    exact this (Ideal.mem_span_singleton_self α)
  refine ⟨b, (D⁻¹ * α')⁻¹, by simp [hD, hα'], hbn, ?_⟩
  rw [hb, hX]
  have h1 : (D⁻¹ * α')⁻¹ * α' * D⁻¹ = 1 := by field_simp
  symm
  calc FractionalIdeal.spanSingleton O⁰ (D⁻¹ * α')⁻¹ *
        (FractionalIdeal.spanSingleton O⁰ α' * (↑I * FractionalIdeal.spanSingleton O⁰ D⁻¹))
      = FractionalIdeal.spanSingleton O⁰ (D⁻¹ * α')⁻¹ * FractionalIdeal.spanSingleton O⁰ α' *
          FractionalIdeal.spanSingleton O⁰ D⁻¹ * ↑I := by ring
    _ = FractionalIdeal.spanSingleton O⁰ ((D⁻¹ * α')⁻¹ * α' * D⁻¹) * ↑I := by
        rw [map_mul, map_mul]
    _ = ↑I := by rw [h1, map_one, one_mul]

/-- **Primes of a quadratic order.** Let $O$ be an order in a number field $K$ of degree
$[K : \mathbb{Q}] = 2$, and let $\mathfrak{p} \neq 0$ be a prime ideal of $O$. Then
$\mathfrak{p}$ contains a rational prime $p$, and either $\#(O/\mathfrak{p}) = p$ or
$\mathfrak{p} = pO$.

The proof: $p$ is the characteristic of the finite domain $O/\mathfrak{p}$, so
$\#(O/\mathfrak{p})$ divides $\#(O/pO) = p^2$ (`NumberField.IsOrder.natCard_quotient_natCast`),
and index $p^2$ forces $\mathfrak{p} = pO$. Compare K. Conrad, *The conductor ideal of an order*,
Corollary 3.9 (p. 7), which matches such primes coprime to the conductor with primes of
$\mathcal{O}_K$. -/
theorem natCard_quotient_eq_or_eq_span_of_finrank_eq_two (hO : NumberField.IsOrder K O)
    (hK : Module.finrank ℚ K = 2) {p : Ideal O} [p.IsPrime] (hp0 : p ≠ ⊥) :
    ∃ q : ℕ, q.Prime ∧ (q : O) ∈ p ∧
      (Nat.card (O ⧸ p) = q ∨ p = Ideal.span {(q : O)}) := by
  have := hO.finite_quotient hp0
  obtain ⟨q, hchar⟩ := CharP.exists (O ⧸ p)
  have hq : q.Prime := CharP.char_is_prime (O ⧸ p) q
  have hqp : (q : O) ∈ p := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ q
  refine ⟨q, hq, hqp, ?_⟩
  have hdvd := hO.natCard_quotient_dvd_pow hq.pos hqp
  rw [hK] at hdvd
  obtain ⟨k, hk, hcard⟩ := (Nat.dvd_prime_pow hq).mp hdvd
  interval_cases k
  · exfalso
    rw [pow_zero] at hcard
    have := Finite.one_lt_card (α := O ⧸ p)
    omega
  · left
    rw [hcard, pow_one]
  · right
    have hle : Ideal.span {(q : O)} ≤ p := (Ideal.span_singleton_le_iff_mem _).mpr hqp
    refine (eq_of_le_of_not_lt hle fun hlt => ?_).symm
    have hcq : Nat.card (O ⧸ Ideal.span {(q : O)}) = q ^ 2 := by
      rw [hO.natCard_quotient_natCast hq.pos, hK]
    have hne : Nat.card (O ⧸ Ideal.span {(q : O)}) ≠ 0 := by
      rw [hcq]
      exact pow_ne_zero 2 hq.ne_zero
    have : (Ideal.span {(q : O)}).toAddSubgroup.FiniteIndex := ⟨hne⟩
    have hlt' : Nat.card (O ⧸ p) < Nat.card (O ⧸ Ideal.span {(q : O)}) := by
      rw [← Submodule.cardQuot_apply, ← Submodule.cardQuot_apply]
      exact AddSubgroup.index_strictAnti (Submodule.toAddSubgroup_strictMono hlt)
    omega

/-- A finite product of principal ideals generated by nonzero elements is a principal
fractional ideal with a nonzero generator. -/
private theorem exists_coeIdeal_multiset_prod_eq_spanSingleton [IsFractionRing O K]
    (t : Multiset (Ideal O)) (ht : ∀ p ∈ t, ∃ w : O, w ≠ 0 ∧ p = Ideal.span {w}) :
    ∃ y : K, y ≠ 0 ∧
      ((t.prod : Ideal O) : FractionalIdeal O⁰ K) = FractionalIdeal.spanSingleton O⁰ y := by
  induction t using Multiset.induction_on with
  | empty =>
    refine ⟨1, one_ne_zero, ?_⟩
    rw [Multiset.prod_zero, Ideal.one_eq_top, FractionalIdeal.coeIdeal_top, map_one]
  | cons p t ih =>
    obtain ⟨y, hy, hty⟩ := ih fun q hq => ht q (Multiset.mem_cons_of_mem hq)
    obtain ⟨w, hw, rfl⟩ := ht p (Multiset.mem_cons_self _ _)
    refine ⟨algebraMap O K w * y,
      mul_ne_zero ((map_ne_zero_iff _ (IsFractionRing.injective O K)).mpr hw) hy, ?_⟩
    rw [Multiset.prod_cons, FractionalIdeal.coeIdeal_mul, hty,
      FractionalIdeal.coeIdeal_span_singleton, map_mul]

/-- **M3, ideal form: invertible ideals of a quadratic order up to scalars are products of
primes of prime norm.** Let $O$ be an order in a number field $K$ of degree
$[K : \mathbb{Q}] = 2$ (for instance an imaginary quadratic field), with conductor
$\mathfrak{c} = \{x \in \mathcal{O}_K : x\mathcal{O}_K \subseteq O\}$ (pulled back to $O$), and
let $M \geq 1$ be an integer. Then every invertible fractional ideal $I$ of $O$ is
$I = x\,\mathfrak{p}_1 \cdots \mathfrak{p}_r$ with $x \in K$, $x \neq 0$, and prime ideals
$\mathfrak{p}_i$ of $O$, each invertible as a fractional ideal, coprime to $\mathfrak{c}$
($\mathfrak{p}_i + \mathfrak{c} = O$), and of prime norm $\#(O/\mathfrak{p}_i) = p_i$ with
$p_i \nmid M$.

This is the elementary route to a weak form of A. V. Sutherland, *18.783 Elliptic Curves*, Fall
2025, Lecture 20, Theorem 20.11 (p. 6: "Every ideal class in cl(O) contains infinitely many ideals
of prime norm"), which Sutherland proves by citing Cox, *Primes of the form* $x^2 + ny^2$,
Theorems 7.7 and 9.12. Proof: by K. Conrad,
*The conductor ideal of an order*, Theorem 5.2(1) (p. 14;
`NumberField.IsOrder.exists_eq_spanSingleton_mul_of_ne_bot`), $I = x\mathfrak{b}$ with
$\mathfrak{b}$ an ideal of $O$ coprime to $M$ and to $\mathfrak{c}$; by Conrad, Theorem 3.6
(p. 6; `NumberField.IsOrder.prod_and_isUnit_of_sup_conductor_eq_top`), $\mathfrak{b}$ is a
product of invertible primes, each coprime to $M\mathfrak{c}$; a factor of norm not prime is
$pO$ (`NumberField.IsOrder.natCard_quotient_eq_or_eq_span_of_finrank_eq_two`) and is moved
into $x$. The instance `IsFractionRing O K` follows from `hO` and is assumed only to state the
identity with `FractionalIdeal.spanSingleton`. -/
theorem exists_eq_spanSingleton_mul_prod_of_finrank_eq_two [IsFractionRing O K]
    (hO : NumberField.IsOrder K O)
    (hK : Module.finrank ℚ K = 2) {M : ℕ} (hM : 0 < M) (I : (FractionalIdeal O⁰ K)ˣ) :
    ∃ (x : K) (s : Multiset (Ideal O)), x ≠ 0 ∧
      (∀ p ∈ s, p.IsPrime ∧ IsUnit (p : FractionalIdeal O⁰ K) ∧
        (Nat.card (O ⧸ p)).Prime ∧ ¬ Nat.card (O ⧸ p) ∣ M ∧
        p ⊔ ((O.comap (integralClosure ℤ K).val).conductorIdeal).comap
          (Subalgebra.inclusion hO.le_integralClosure) = ⊤) ∧
      (I : FractionalIdeal O⁰ K) =
        FractionalIdeal.spanSingleton O⁰ x * ((s.prod : Ideal O) : FractionalIdeal O⁰ K) := by
  classical
  set c := ((O.comap (integralClosure ℤ K).val).conductorIdeal).comap
    (Subalgebra.inclusion hO.le_integralClosure) with hc
  obtain ⟨z, hz0, hzc⟩ := exists_ne_zero_mem_conductor hO
  have hM0 : (M : O) ≠ 0 := by
    intro h
    have h' : ((M : O) : K) = 0 := by rw [h]; rfl
    push_cast at h'
    exact hM.ne' (by exact_mod_cast h')
  set n := Ideal.span {(M : O) * z} with hn
  have hn0 : n ≠ ⊥ := by
    rw [hn, Ne, Ideal.span_singleton_eq_bot]
    exact mul_ne_zero hM0 hz0
  obtain ⟨b, x, hx, hbn, hI⟩ := hO.exists_eq_spanSingleton_mul_of_ne_bot I hn0
  have hbM : b ⊔ Ideal.span {(M : O)} = ⊤ := by
    refine top_unique (hbn ▸ sup_le_sup_left ?_ b)
    exact (Ideal.span_singleton_le_iff_mem _).mpr
      (Ideal.mem_span_singleton.mpr (dvd_mul_right _ _))
  have hbc : b ⊔ c = ⊤ := by
    refine top_unique (hbn ▸ sup_le_sup_left ?_ b)
    exact (Ideal.span_singleton_le_iff_mem _).mpr (Ideal.mul_mem_left c _ hzc)
  have hb0 : b ≠ ⊥ := by
    rintro rfl
    rw [FractionalIdeal.coeIdeal_bot, mul_zero] at hI
    have h1 : (↑I : FractionalIdeal O⁰ K) * ↑I⁻¹ = 1 := Units.mul_inv I
    rw [hI, zero_mul] at h1
    exact zero_ne_one h1
  obtain ⟨⟨s₀, hs₀, hprod⟩, -⟩ := hO.prod_and_isUnit_of_sup_conductor_eq_top hb0 hbc
  have hle : ∀ p ∈ s₀, b ≤ p := by
    intro p hp
    rw [← hprod, ← Multiset.cons_erase hp, Multiset.prod_cons]
    exact Ideal.mul_le_left
  have hcop : ∀ p ∈ s₀, p ≠ ⊥ ∧ p ⊔ Ideal.span {(M : O)} = ⊤ ∧ p ⊔ c = ⊤ := by
    intro p hp
    refine ⟨fun h => hb0 (le_bot_iff.mp (h ▸ hle p hp)), ?_, ?_⟩
    · exact top_unique (hbM ▸ sup_le_sup_right (hle p hp) _)
    · exact top_unique (hbc ▸ sup_le_sup_right (hle p hp) _)
  obtain ⟨y, hy, hty⟩ := exists_coeIdeal_multiset_prod_eq_spanSingleton (K := K)
    (s₀.filter fun p => ¬ (Nat.card (O ⧸ p)).Prime) (by
      intro p hp
      obtain ⟨hps, hpr⟩ := Multiset.mem_filter.mp hp
      have := (hs₀ p hps).1
      obtain ⟨q, hq, -, hcase⟩ :=
        hO.natCard_quotient_eq_or_eq_span_of_finrank_eq_two hK (hcop p hps).1
      rcases hcase with hcard | hspan
      · exact absurd (hcard ▸ hq) hpr
      · refine ⟨(q : O), ?_, hspan⟩
        intro h0
        apply (hcop p hps).1
        rw [hspan, h0, Ideal.span_singleton_eq_bot])
  refine ⟨x * y, (s₀.filter fun p => (Nat.card (O ⧸ p)).Prime), mul_ne_zero hx hy, ?_, ?_⟩
  · intro p hp
    obtain ⟨hps, hpr⟩ := Multiset.mem_filter.mp hp
    have hpp := (hs₀ p hps).1
    refine ⟨hpp, (hs₀ p hps).2, hpr, ?_, (hcop p hps).2.2⟩
    obtain ⟨q, hq, hqp, hcase⟩ :=
      hO.natCard_quotient_eq_or_eq_span_of_finrank_eq_two hK (hcop p hps).1
    have hcard : Nat.card (O ⧸ p) = q := by
      rcases hcase with hcard | hspan
      · exact hcard
      · exfalso
        rw [hspan, hO.natCard_quotient_natCast hq.pos, hK, sq, Nat.prime_mul_iff] at hpr
        have := hq.one_lt
        omega
    rw [hcard]
    rintro ⟨k, rfl⟩
    apply hpp.ne_top
    have hMp : ((q * k : ℕ) : O) ∈ p := by
      rw [Nat.cast_mul]
      exact Ideal.mul_mem_right _ _ hqp
    have := (hcop p hps).2.1
    rwa [sup_eq_left.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hMp)] at this
  · rw [hI, ← hprod, ← Multiset.prod_filter_mul_prod_filter_not
      (fun p => (Nat.card (O ⧸ p)).Prime) (s := s₀), FractionalIdeal.coeIdeal_mul, hty, map_mul]
    ring

/-- **M3: the class group of a quadratic order is generated by primes of prime norm.** Let $O$
be an order in a number field $K$ of degree $[K : \mathbb{Q}] = 2$ (for instance an imaginary
quadratic field), let $\mathrm{Cl}(O)$ be its class group (`ClassGroup O`: invertible fractional
ideals of $O$ modulo principal ones), and let $M \geq 1$ be an integer. Let $G \subseteq
\mathrm{Cl}(O)$ be the set of classes $[\mathfrak{p}]$ of the prime ideals $\mathfrak{p}$ of $O$
that are invertible as fractional ideals and have prime norm $p = \#(O/\mathfrak{p})$ with
$p \nmid M$. Then $G$ generates $\mathrm{Cl}(O)$, already as a monoid: every class is a product
of elements of $G$.

Taking for $M$ a multiple of the discriminant and of the conductor leaves only primes above
split rational primes. This is the generation statement that replaces A. V. Sutherland,
*18.783 Elliptic Curves*, Fall 2025, Lecture 20, Theorem 20.11 (p. 6), in the route to the
irreducibility of the Hilbert class polynomial; the class group is Sutherland's $\mathrm{cl}(O)$
by Lecture 17, Corollary 17.11 (p. 5), and K. Conrad's $\mathrm{Cl}(O)$ (*The conductor ideal of
an order*, §5, p. 13). It follows from
`NumberField.IsOrder.exists_eq_spanSingleton_mul_prod_of_finrank_eq_two`. The instance
`IsFractionRing O K` follows from `hO`; `ClassGroup.mk` needs it. -/
theorem closure_classGroup_mk_eq_top [IsFractionRing O K] (hO : NumberField.IsOrder K O)
    (hK : Module.finrank ℚ K = 2) {M : ℕ} (hM : 0 < M) :
    Submonoid.closure {C : ClassGroup O | ∃ (p : Ideal O) (u : (FractionalIdeal O⁰ K)ˣ),
      p.IsPrime ∧ (u : FractionalIdeal O⁰ K) = p ∧ (Nat.card (O ⧸ p)).Prime ∧
        ¬ Nat.card (O ⧸ p) ∣ M ∧ ClassGroup.mk K u = C} = ⊤ ∧
    Subgroup.closure {C : ClassGroup O | ∃ (p : Ideal O) (u : (FractionalIdeal O⁰ K)ˣ),
      p.IsPrime ∧ (u : FractionalIdeal O⁰ K) = p ∧ (Nat.card (O ⧸ p)).Prime ∧
        ¬ Nat.card (O ⧸ p) ∣ M ∧ ClassGroup.mk K u = C} = ⊤ := by
  set G := {C : ClassGroup O | ∃ (p : Ideal O) (u : (FractionalIdeal O⁰ K)ˣ),
    p.IsPrime ∧ (u : FractionalIdeal O⁰ K) = p ∧ (Nat.card (O ⧸ p)).Prime ∧
      ¬ Nat.card (O ⧸ p) ∣ M ∧ ClassGroup.mk K u = C} with hG
  have key : ∀ C : ClassGroup O, C ∈ Submonoid.closure G := by
    intro C
    refine ClassGroup.induction K (fun u => ?_) C
    obtain ⟨x, s, hx, hs, hu⟩ := hO.exists_eq_spanSingleton_mul_prod_of_finrank_eq_two hK hM u
    have hprod : ∀ t : Multiset (Ideal O), (∀ p ∈ t, p ∈ s) →
        ∀ h : IsUnit ((t.prod : Ideal O) : FractionalIdeal O⁰ K),
          ClassGroup.mk K h.unit ∈ Submonoid.closure G := by
      intro t
      induction t using Multiset.induction_on with
      | empty =>
        intro _ h
        have : h.unit = 1 := Units.ext (by
          rw [IsUnit.unit_spec, Multiset.prod_zero, Ideal.one_eq_top,
            FractionalIdeal.coeIdeal_top, Units.val_one])
        rw [this, map_one]
        exact one_mem _
      | cons p t ih =>
        intro hts h
        have hp := hs p (hts p (Multiset.mem_cons_self _ _))
        have hpu : IsUnit (p : FractionalIdeal O⁰ K) := hp.2.1
        have htu : IsUnit ((t.prod : Ideal O) : FractionalIdeal O⁰ K) := by
          rw [Multiset.prod_cons, FractionalIdeal.coeIdeal_mul] at h
          exact isUnit_of_mul_isUnit_right h
        have : h.unit = hpu.unit * htu.unit := Units.ext (by
          rw [IsUnit.unit_spec, Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec,
            Multiset.prod_cons, FractionalIdeal.coeIdeal_mul])
        rw [this, map_mul]
        exact mul_mem (Submonoid.subset_closure ⟨p, hpu.unit, hp.1, IsUnit.unit_spec _,
          hp.2.2.1, hp.2.2.2.1, rfl⟩) (ih (fun q hq => hts q (Multiset.mem_cons_of_mem hq)) htu)
    have hxu : IsUnit (FractionalIdeal.spanSingleton O⁰ x) :=
      IsUnit.of_mul_eq_one (FractionalIdeal.spanSingleton O⁰ x⁻¹)
        (by rw [← map_mul, mul_inv_cancel₀ hx, map_one])
    have hsu : IsUnit ((s.prod : Ideal O) : FractionalIdeal O⁰ K) := by
      have := u.isUnit
      rw [hu] at this
      exact isUnit_of_mul_isUnit_right this
    have hux : u = hxu.unit * hsu.unit := Units.ext (by
      rw [Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec, hu])
    have hx1 : ClassGroup.mk K hxu.unit = 1 := by
      rw [ClassGroup.mk_eq_one_iff, IsUnit.unit_spec,
        FractionalIdeal.coeToSubmodule_spanSingleton]
      exact ⟨x, rfl⟩
    rw [hux, map_mul, hx1, one_mul]
    exact hprod s (fun _ h => h) hsu
  refine ⟨eq_top_iff.mpr fun C _ => key C, eq_top_iff.mpr fun C _ => ?_⟩
  exact (Submonoid.closure_le (S := (Subgroup.closure G).toSubmonoid)).mpr
    Subgroup.subset_closure (key C)

end NumberField.IsOrder

end
