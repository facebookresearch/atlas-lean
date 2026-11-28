/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.OrderClassGroup
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian

@[expose] public section

set_option autoImplicit false

/-!
# Ideal classes of an order prime to a given ideal, and surjectivity of `Cl(O) → Cl(𝒪_K)`

Let `O` be an order of a number field `K` (`NumberField.IsOrder K O`) and `𝒪_K` the ring of
integers `integralClosure ℤ K`. We prove (K. Conrad, *The conductor ideal of an order*,
Theorem 5.2 and its proof, pp. 14–15):

* `ClassGroup.exists_isUnit_coeIdeal_sup_eq_top`: in a Noetherian domain `R` of dimension at
  most one, for every nonzero ideal `𝔫`, every ideal class has a representative that is an
  invertible integral ideal `𝔟` with `𝔟 + 𝔫 = R`;
* `NumberField.IsOrder.exists_isUnit_coeIdeal_sup_eq_top`: the same for an order `O`
  (Conrad, Theorem 5.2(1)), and `NumberField.exists_isUnit_coeIdeal_sup_eq_top_integralClosure`
  for `𝒪_K`;
* `NumberField.IsOrder.conductorIdeal_ne_bot`: the conductor of `O` is a nonzero ideal of `𝒪_K`;
* `NumberField.IsOrder.classGroupMap_surjective`: the map `Cl(O) → Cl(𝒪_K)`,
  `[𝔟] ↦ [𝔟𝒪_K]`, is surjective (Conrad, Theorem 5.2(2)).
-/

open scoped nonZeroDivisors

section DimensionLEOne

variable {R K : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]

/-- Chinese remainder theorem for an invertible fractional ideal `𝔞` (Conrad, proof of
Theorem 5.2(1), p. 15, surjectivity of (5.2)): for finitely many pairwise coprime proper ideals
`𝔭ᵢ`, some `x ∈ 𝔞` lies in no `𝔭ᵢ𝔞`. -/
private theorem exists_mem_forall_notMem_mul (S : Finset (Ideal R))
    (hS : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → p ⊔ q = ⊤) (hS1 : ∀ p ∈ S, p ≠ ⊤)
    (a : (FractionalIdeal R⁰ K)ˣ) :
    ∃ x ∈ (a : FractionalIdeal R⁰ K), ∀ p ∈ S, x ∉ (p : FractionalIdeal R⁰ K) * a := by
  classical
  have hy : ∀ p ∈ S, ∃ y ∈ (a : FractionalIdeal R⁰ K), y ∉ (p : FractionalIdeal R⁰ K) * a := by
    intro p hp
    by_contra! h
    apply hS1 p hp
    have hle : (a : FractionalIdeal R⁰ K) ≤ p * a := fun y hy => h y hy
    have h1 : ((⊤ : Ideal R) : FractionalIdeal R⁰ K) ≤ p :=
      calc ((⊤ : Ideal R) : FractionalIdeal R⁰ K) = a * ↑a⁻¹ := by
            rw [FractionalIdeal.coeIdeal_top, Units.mul_inv]
        _ ≤ p * a * ↑a⁻¹ := mul_le_mul_left hle _
        _ = p := by rw [mul_assoc, Units.mul_inv, mul_one]
    exact top_unique ((FractionalIdeal.coeIdeal_le_coeIdeal K).mp h1)
  choose! y hya hyp using hy
  have hβ : ∀ p ∈ S, ∃ β : R, β - 1 ∈ p ∧ ∀ q ∈ S.erase p, β ∈ q := by
    intro p hp
    have htop : p ⊔ ∏ q ∈ S.erase p, q = ⊤ := Ideal.sup_prod_eq_top fun q hq =>
      hS p hp q (Finset.mem_of_mem_erase hq) (Finset.ne_of_mem_erase hq).symm
    obtain ⟨α, hα, β, hβ, hαβ⟩ := Submodule.mem_sup.mp (htop ▸ Submodule.mem_top (x := (1 : R)))
    refine ⟨β, ?_, fun q hq => ?_⟩
    · have : β - 1 = -α := by rw [← hαβ]; ring
      rw [this]
      exact p.neg_mem hα
    · rw [← Finset.mul_prod_erase _ (fun q => q) hq] at hβ
      exact Ideal.mul_le_left hβ
  choose! β hβ1 hβS using hβ
  refine ⟨∑ p ∈ S, algebraMap R K (β p) * y p, ?_, fun p hp hmem => hyp p hp ?_⟩
  · exact Submodule.sum_mem _ fun p hp => by
      rw [← Algebra.smul_def]
      exact Submodule.smul_mem _ _ (hya p hp)
  · have e : y p = ∑ q ∈ S, algebraMap R K (β q) * y q -
        ∑ q ∈ S.erase p, algebraMap R K (β q) * y q - algebraMap R K (β p - 1) * y p := by
      rw [← Finset.add_sum_erase S _ hp, map_sub, map_one]
      ring
    rw [e]
    refine Submodule.sub_mem _ (Submodule.sub_mem _ hmem (Submodule.sum_mem _ fun q hq => ?_)) ?_
    · have hqS := Finset.mem_of_mem_erase hq
      exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _
        (hβS q hqS p (Finset.mem_erase.mpr ⟨(Finset.ne_of_mem_erase hq).symm, hp⟩))) (hya q hqS)
    · exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_coeIdeal_of_mem _ (hβ1 p hp))
        (hya p hp)

/-- **Ideal classes have representatives prime to a given ideal.** Let $R$ be a Noetherian
integral domain of dimension at most one (every nonzero prime ideal is maximal) with fraction
field $K$, and let $\mathfrak{n}$ be a nonzero ideal of $R$. Then every class $x$ in the class
group $\mathrm{Cl}(R)$ (invertible fractional ideals modulo principal ones) is the class of an
ideal $\mathfrak{b}$ of $R$ that is invertible as a fractional ideal and satisfies
$\mathfrak{b} + \mathfrak{n} = R$.

This is K. Conrad, *The conductor ideal of an order*, Theorem 5.2(1) (p. 14), stated there for
orders in a number field, with its proof (pp. 14–15), which uses only that the ring is a
Noetherian domain of dimension at most one: write the class as $[\mathfrak{a}]^{-1}$; the primes
$\mathfrak{p}_1, \dots, \mathfrak{p}_r$ containing $\mathfrak{n}$ are finitely many (here:
they are minimal primes of $\mathfrak{n}$ in a Noetherian ring; Conrad's footnote 5, p. 14: "The
finiteness of the number of prime ideals containing n is true when O is an arbitrary
one-dimensional Noetherian domain"); an $x \in \mathfrak{a}$ with
$x \notin \mathfrak{p}_i\mathfrak{a}$ for all $i$ exists by the Chinese remainder theorem for
modules ((5.2), p. 15), and $\mathfrak{b} = x\mathfrak{a}^{-1}$ works. -/
theorem ClassGroup.exists_isUnit_coeIdeal_sup_eq_top [IsNoetherianRing R]
    [Ring.DimensionLEOne R] {n : Ideal R} (hn : n ≠ ⊥) (x : ClassGroup R) :
    ∃ (b : Ideal R) (hb : IsUnit (b : FractionalIdeal R⁰ K)), b ⊔ n = ⊤ ∧
      ClassGroup.mk K hb.unit = x := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, ClassGroup.mk K a = x⁻¹ :=
    ClassGroup.induction K (P := fun z => ∃ a, ClassGroup.mk K a = z) (fun I => ⟨I, rfl⟩) x⁻¹
  set S := (Ideal.finite_minimalPrimes_of_isNoetherianRing R n).toFinset with hSdef
  have hSmem : ∀ p, p ∈ S ↔ p ∈ n.minimalPrimes := fun p => Set.Finite.mem_toFinset _
  have hSmax : ∀ p ∈ S, p.IsMaximal := by
    intro p hp
    have hp' := ((hSmem p).mp hp).1
    exact Ring.DimensionLEOne.maximalOfPrime (fun h => hn (le_bot_iff.mp (h ▸ hp'.2))) hp'.1
  have hmaxS : ∀ m : Ideal R, m.IsMaximal → n ≤ m → m ∈ S := by
    intro m hm hnm
    rw [hSmem]
    refine ⟨⟨hm.isPrime, hnm⟩, fun q hq hqm => ?_⟩
    have hq0 : q ≠ ⊥ := fun h => hn (le_bot_iff.mp (h ▸ hq.2))
    exact ((Ring.DimensionLEOne.maximalOfPrime hq0 hq.1).eq_of_le hm.ne_top hqm).ge
  obtain ⟨x0, hx0a, hx00, hx0S⟩ : ∃ x0 ∈ (a : FractionalIdeal R⁰ K), x0 ≠ 0 ∧
      ∀ p ∈ S, x0 ∉ (p : FractionalIdeal R⁰ K) * a := by
    by_cases hS : S = ∅
    · obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
        (p := ((a : FractionalIdeal R⁰ K) : Submodule R K))
        (by rw [Ne, FractionalIdeal.coeToSubmodule_eq_bot]; exact a.ne_zero)
      exact ⟨z, hz, hz0, by simp [hS]⟩
    · obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hS
      obtain ⟨z, hz, hzS⟩ := exists_mem_forall_notMem_mul S
        (fun p hp q hq hpq => Ideal.IsMaximal.coprime_of_ne (hSmax p hp) (hSmax q hq) hpq)
        (fun p hp => (hSmax p hp).ne_top) a
      refine ⟨z, hz, fun h0 => hzS p hp ?_, hzS⟩
      rw [h0]
      exact Submodule.zero_mem _
  have hspan : FractionalIdeal.spanSingleton R⁰ x0 * ↑a⁻¹ ≤ 1 :=
    calc FractionalIdeal.spanSingleton R⁰ x0 * ↑a⁻¹ ≤ (a : FractionalIdeal R⁰ K) * ↑a⁻¹ :=
          mul_le_mul_left (FractionalIdeal.spanSingleton_le_iff_mem.mpr hx0a) _
      _ = 1 := Units.mul_inv a
  obtain ⟨b, hb⟩ := FractionalIdeal.le_one_iff_exists_coeIdeal.mp hspan
  have hba : (b : FractionalIdeal R⁰ K) * a = FractionalIdeal.spanSingleton R⁰ x0 := by
    rw [hb, mul_assoc, Units.inv_mul, mul_one]
  have hbu : IsUnit (b : FractionalIdeal R⁰ K) := by
    rw [hb]
    exact ((isUnit_iff_ne_zero.mpr hx00).map (FractionalIdeal.spanSingleton R⁰)).mul
      a⁻¹.isUnit
  refine ⟨b, hbu, ?_, ?_⟩
  · by_contra hbn
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hbn
    apply hx0S m (hmaxS m hm (le_sup_right.trans hle))
    have hmul : (b : FractionalIdeal R⁰ K) * a ≤ (m : FractionalIdeal R⁰ K) * a :=
      mul_le_mul_left ((FractionalIdeal.coeIdeal_le_coeIdeal K).mpr (le_sup_left.trans hle)) _
    rw [hba] at hmul
    exact hmul (FractionalIdeal.mem_spanSingleton_self _ x0)
  · have h1 : ClassGroup.mk K (hbu.unit * a) = 1 := by
      rw [ClassGroup.mk_eq_one_iff]
      have : ((hbu.unit * a : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) =
          FractionalIdeal.spanSingleton R⁰ x0 := by
        rw [Units.val_mul, IsUnit.unit_spec, hba]
      rw [this, FractionalIdeal.coeToSubmodule_spanSingleton]
      exact ⟨⟨x0, rfl⟩⟩
    rw [map_mul, ha] at h1
    rw [eq_inv_of_mul_eq_one_left h1, inv_inv]

end DimensionLEOne

/-- **Ideal classes of the ring of integers prime to a given ideal.** Let $K$ be a number field
with ring of integers $\mathcal{O}_K$ (`integralClosure ℤ K`) and $\mathfrak{n}$ a nonzero ideal
of $\mathcal{O}_K$. Then every class in $\mathrm{Cl}(\mathcal{O}_K)$ is the class of an ideal
$\mathfrak{b}$ of $\mathcal{O}_K$, invertible as a fractional ideal, with
$\mathfrak{b} + \mathfrak{n} = \mathcal{O}_K$.

This is K. Conrad, *The conductor ideal of an order*, Theorem 5.2(1) (p. 14) for the order
$\mathcal{O}_K$, as used in the proof of Theorem 5.2(2) (p. 15); it is
`ClassGroup.exists_isUnit_coeIdeal_sup_eq_top` for the Dedekind domain $\mathcal{O}_K$. -/
theorem NumberField.exists_isUnit_coeIdeal_sup_eq_top_integralClosure (K : Type*) [Field K]
    [NumberField K] {n : Ideal (integralClosure ℤ K)} (hn : n ≠ ⊥)
    (x : ClassGroup (integralClosure ℤ K)) :
    ∃ (b : Ideal (integralClosure ℤ K))
      (hb : IsUnit (b : FractionalIdeal (integralClosure ℤ K)⁰ K)), b ⊔ n = ⊤ ∧
        ClassGroup.mk K hb.unit = x :=
  ClassGroup.exists_isUnit_coeIdeal_sup_eq_top hn x

namespace NumberField.IsOrder

variable {K : Type*} [Field K] [NumberField K] {O : Subalgebra ℤ K}

/-- **The conductor of an order is nonzero.** Let $O$ be an order in a number field $K$, with
ring of integers $\mathcal{O}_K$ (`integralClosure ℤ K`). Then the conductor
$\mathfrak{c} = \{x \in \mathcal{O}_K : x\mathcal{O}_K \subseteq O\}$
(`Subalgebra.conductorIdeal`) is a nonzero ideal of $\mathcal{O}_K$: it contains a nonzero
integer.

K. Conrad, *The conductor ideal of an order*, proof of Theorem 5.2(2) (p. 15): "Let c be the
conductor of O. This is a nonzero ideal in OK". -/
theorem conductorIdeal_ne_bot (hO : NumberField.IsOrder K O) :
    (O.comap (integralClosure ℤ K).val).conductorIdeal ≠ ⊥ := by
  classical
  have := (NumberField.isOrder_integralClosure K).moduleFinite
  have := hO.isLocalization
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ) (M := integralClosure ℤ K)
  obtain ⟨⟨_, d, hd, rfl⟩, hb⟩ := IsLocalization.exist_integer_multiples_of_finset
    (Algebra.algebraMapSubmonoid O ℤ⁰) (s.image fun t : integralClosure ℤ K => (t : K))
  have key : ∀ t ∈ s, (d : K) * (t : K) ∈ O := by
    intro t ht
    obtain ⟨o, ho⟩ := hb (t : K) (Finset.mem_image_of_mem _ ht)
    have e : algebraMap O K o = (d : K) * (t : K) := by
      rw [ho, Algebra.smul_def]
      simp
    rw [← e]
    exact o.2
  have key' : ∀ t : integralClosure ℤ K, (d : K) * (t : K) ∈ O := by
    intro t
    have ht : t ∈ Submodule.span ℤ (s : Set (integralClosure ℤ K)) := by
      rw [hs]
      exact Submodule.mem_top
    induction ht using Submodule.span_induction with
    | mem x hx => exact key x hx
    | zero => simp
    | add x y _ _ hx hy =>
      rw [Subalgebra.coe_add, mul_add]
      exact O.add_mem hx hy
    | smul m x _ hx =>
      rw [Subalgebra.coe_smul, mul_smul_comm]
      exact O.smul_mem hx m
  refine (Submodule.ne_bot_iff _).mpr ⟨(d : integralClosure ℤ K), fun t => ?_, ?_⟩
  · rw [Subalgebra.mem_comap]
    simpa using key' t
  · intro h
    apply nonZeroDivisors.ne_zero hd
    have h' := congrArg (fun z : integralClosure ℤ K => (z : K)) h
    simpa using h'

variable [IsFractionRing O K]

/-- **Ideal classes of an order prime to a given ideal.** Let $O$ be an order in a number field
$K$ (`NumberField.IsOrder`) and $\mathfrak{n}$ a nonzero ideal of $O$. Then every class $x$ in
the ideal class group $\mathrm{Cl}(O)$ (invertible fractional ideals of $O$ modulo principal
ones) is the class of an ideal $\mathfrak{b}$ of $O$ that is invertible as a fractional ideal
and satisfies $\mathfrak{b} + \mathfrak{n} = O$.

This is K. Conrad, *The conductor ideal of an order*, Theorem 5.2(1) (p. 14): "For each nonzero
ideal n in O, every ideal class in Cl(O) has a representative that is an ideal in O and is
relatively prime to n", with the proof on pp. 14–15; here the representative is moreover
invertible, and the result is `ClassGroup.exists_isUnit_coeIdeal_sup_eq_top`, as $O$ is
Noetherian of dimension at most one (`NumberField.IsOrder.isNoetherianRing`,
`NumberField.IsOrder.dimensionLEOne`). -/
theorem exists_isUnit_coeIdeal_sup_eq_top (hO : NumberField.IsOrder K O) {n : Ideal O}
    (hn : n ≠ ⊥) (x : ClassGroup O) :
    ∃ (b : Ideal O) (hb : IsUnit (b : FractionalIdeal O⁰ K)), b ⊔ n = ⊤ ∧
      ClassGroup.mk K hb.unit = x := by
  have := hO.isNoetherianRing
  have := hO.dimensionLEOne
  exact ClassGroup.exists_isUnit_coeIdeal_sup_eq_top hn x

/-- **The map of class groups of an order is surjective.** Let $O$ be an order in a number field
$K$ with ring of integers $\mathcal{O}_K$ (`integralClosure ℤ K`). Then the group homomorphism
$\mathrm{Cl}(O) \to \mathrm{Cl}(\mathcal{O}_K)$,
$[\mathfrak{b}] \mapsto [\mathfrak{b}\mathcal{O}_K]$ (`NumberField.IsOrder.classGroupMap`), is
surjective.

This is K. Conrad, *The conductor ideal of an order*, Theorem 5.2(2) (p. 14), with the proof on
p. 15: a class of $\mathrm{Cl}(\mathcal{O}_K)$ is $[\mathfrak{a}]$ with $\mathfrak{a}$ an ideal
prime to the conductor $\mathfrak{c}$
(`NumberField.exists_isUnit_coeIdeal_sup_eq_top_integralClosure`,
`NumberField.IsOrder.conductorIdeal_ne_bot`); then, in Conrad's words, "By Theorems 3.6 and 3.8,
$\mathfrak{a} \cap O$ is relatively prime to $\mathfrak{c}$ in $O$, is an invertible fractional
$O$-ideal, and $\mathfrak{a} = (\mathfrak{a} \cap O)\mathcal{O}_K$"
(`NumberField.IsOrder.sup_comap_eq_top_of_sup_eq_top`,
`NumberField.IsOrder.prod_and_isUnit_of_sup_conductor_eq_top`,
`NumberField.IsOrder.map_comap_eq_of_sup_eq_top`). -/
theorem classGroupMap_surjective (hO : NumberField.IsOrder K O) :
    Function.Surjective (classGroupMap hO) := by
  intro y
  obtain ⟨a, ha, hac, rfl⟩ :=
    NumberField.exists_isUnit_coeIdeal_sup_eq_top_integralClosure K hO.conductorIdeal_ne_bot y
  have ha0 : a ≠ ⊥ := by
    rintro rfl
    rw [FractionalIdeal.coeIdeal_bot] at ha
    exact not_isUnit_zero ha
  have hbc := hO.sup_comap_eq_top_of_sup_eq_top hac
  have hb0 : a.comap (Subalgebra.inclusion hO.le_integralClosure) ≠ ⊥ :=
    hO.ideals_coprime_conductor.2.2.1 a hac ha0
  have hbu := (hO.prod_and_isUnit_of_sup_conductor_eq_top hb0 hbc).2
  refine ⟨ClassGroup.mk K hbu.unit, ?_⟩
  rw [classGroupMap_mk]
  congr 1
  ext1
  rw [Units.coe_map, IsUnit.unit_spec, IsUnit.unit_spec]
  change hO.extendFractionalIdeal _ = _
  rw [extendFractionalIdeal_coeIdeal]
  exact congrArg _ (hO.map_comap_eq_of_sup_eq_top hac)

end NumberField.IsOrder

end
