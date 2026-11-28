/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.OrderClassGroup
public import MathlibExt.NumberTheory.NumberField.OrderConductorCorrespondence
public import MathlibExt.NumberTheory.NumberField.OrderInvertibleIdeals
public import MathlibExt.RingTheory.ClassGroup.CoprimeInvertibleRepresentative

@[expose] public section

set_option autoImplicit false

/-!
# Ideal classes of an order prime to a given ideal, and surjectivity of `Cl(O) → Cl(𝒪_K)`

Let `O` be an order of a number field `K` (`NumberField.IsOrder K O`) and `𝒪_K` the ring of
integers `integralClosure ℤ K`. We prove (K. Conrad, *The conductor ideal of an order*,
Theorem 5.2 and its proof, pp. 14–15):

* `NumberField.IsOrder.exists_isUnit_coeIdeal_sup_eq_top`: for every nonzero ideal `𝔫` of `O`,
  every ideal class of `O` has a representative that is an invertible integral ideal `𝔟` with
  `𝔟 + 𝔫 = O` (Conrad, Theorem 5.2(1)); this is the case of an order of
  `ClassGroup.exists_isUnit_coeIdeal_sup_eq_top`, for Noetherian domains of dimension at most one;
* `NumberField.IsOrder.conductorIdeal_ne_bot`: the conductor of `O` is a nonzero ideal of `𝒪_K`;
* `NumberField.IsOrder.classGroup_map_surjective`: the map `Cl(O) → Cl(𝒪_K)`,
  `[𝔟] ↦ [𝔟𝒪_K]`, which is Mathlib's `ClassGroup.map` for the inclusion `O → 𝒪_K`, is
  surjective (Conrad, Theorem 5.2(2)).
-/

open scoped nonZeroDivisors

namespace NumberField.IsOrder

variable {K : Type*} [Field K] [NumberField K] {O : Subalgebra ℤ K}

/-- **The conductor of an order is nonzero.** Let $O$ be an order in a number field $K$, with
ring of integers $\mathcal{O}_K$ (`integralClosure ℤ K`). Then the conductor
$\mathfrak{c} = \{x \in \mathcal{O}_K : x\mathcal{O}_K \subseteq O\}$
(`Subalgebra.conductorIdeal`) is a nonzero ideal of $\mathcal{O}_K$.

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

variable [IsFractionRing O K] in
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
  exact ClassGroup.exists_isUnit_coeIdeal_sup_eq_top K hn x

/-- **The map of class groups of an order is surjective.** Let $O$ be an order in a number field
$K$ with ring of integers $\mathcal{O}_K$ (`integralClosure ℤ K`). Then the group homomorphism
$\mathrm{Cl}(O) \to \mathrm{Cl}(\mathcal{O}_K)$,
$[\mathfrak{b}] \mapsto [\mathfrak{b}\mathcal{O}_K]$, induced by the inclusion
$O \subseteq \mathcal{O}_K$ (`ClassGroup.map`), is surjective.

This is K. Conrad, *The conductor ideal of an order*, Theorem 5.2(2) (p. 14), with the proof on
p. 15: a class of $\mathrm{Cl}(\mathcal{O}_K)$ is $[\mathfrak{a}]$ with $\mathfrak{a}$ an ideal
prime to the conductor $\mathfrak{c}$ (`ClassGroup.exists_isUnit_coeIdeal_sup_eq_top`,
`NumberField.IsOrder.conductorIdeal_ne_bot`); then, in Conrad's words, "By Theorems 3.6 and 3.8,
$\mathfrak{a} \cap O$ is relatively prime to $\mathfrak{c}$ in $O$, is an invertible fractional
$O$-ideal, and $\mathfrak{a} = (\mathfrak{a} \cap O)\mathcal{O}_K$"
(`NumberField.IsOrder.sup_comap_eq_top_of_sup_eq_top`,
`NumberField.IsOrder.prod_and_isUnit_of_sup_conductor_eq_top`,
`NumberField.IsOrder.map_comap_eq_of_sup_eq_top`). -/
theorem classGroup_map_surjective (hO : NumberField.IsOrder K O) :
    Function.Surjective (ClassGroup.map (Subalgebra.inclusion hO.le_integralClosure).toRingHom
      (Subalgebra.inclusion_injective hO.le_integralClosure)) := by
  intro y
  obtain ⟨a, ha, hac, rfl⟩ :=
    ClassGroup.exists_isUnit_coeIdeal_sup_eq_top K hO.conductorIdeal_ne_bot y
  have := hO.isFractionRing
  have ha0 : a ≠ ⊥ := by
    rintro rfl
    rw [FractionalIdeal.coeIdeal_bot] at ha
    exact not_isUnit_zero ha
  have hbc := hO.sup_comap_eq_top_of_sup_eq_top hac
  have hb0 : a.comap (Subalgebra.inclusion hO.le_integralClosure) ≠ ⊥ :=
    hO.ideals_coprime_conductor.2.2.1 a hac ha0
  have hbu := (hO.prod_and_isUnit_of_sup_conductor_eq_top hb0 hbc).2
  refine ⟨ClassGroup.mk K hbu.unit, ?_⟩
  rw [ClassGroup.map_mk K K]
  congr 1
  ext1
  rw [Units.coe_map, IsUnit.unit_spec, IsUnit.unit_spec]
  change FractionalIdeal.extended K _ _ = _
  rw [FractionalIdeal.extended_coeIdeal_eq_map]
  exact congrArg _ (hO.map_comap_eq_of_sup_eq_top hac)

end NumberField.IsOrder

end
