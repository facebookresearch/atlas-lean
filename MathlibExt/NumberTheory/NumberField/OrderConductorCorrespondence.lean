/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.OrderIdeals

@[expose] public section

/-!
# Ideals of an order coprime to the conductor

Let `O` be an order of a number field `K` (`NumberField.IsOrder K O`), let `ι : O → 𝒪_K` be the
inclusion into the ring of integers `𝒪_K = integralClosure ℤ K`, and let `𝔠` be the conductor
of `O`, the ideal `Subalgebra.conductorIdeal` of `𝒪_K` of the elements `x` with `x𝒪_K ⊆ O`.
An ideal `𝔞` of `𝒪_K` is coprime to `𝔠` when `𝔞 ⊔ 𝔠 = ⊤`, and an ideal `𝔟` of `O` is coprime to
`𝔠` when `𝔟 ⊔ 𝔠.comap ι = ⊤`. We prove (K. Conrad, *The conductor ideal of an order*,
Theorem 3.8 and Corollary 3.10, pp. 6–7):

* `NumberField.IsOrder.ideals_coprime_conductor`: contraction `𝔞 ↦ 𝔞 ∩ O` and extension
  `𝔟 ↦ 𝔟𝒪_K` preserve coprimality to `𝔠`, are mutually inverse on coprime ideals, preserve
  nonzero ideals, are multiplicative, and induce ring isomorphisms `O/(𝔞 ∩ O) ≅ 𝒪_K/𝔞` and
  `O/𝔟 ≅ 𝒪_K/𝔟𝒪_K`;
* `NumberField.IsOrder.natCard_quotient_comap_of_sup_eq_top` and
  `NumberField.IsOrder.natCard_quotient_map_of_sup_eq_top`: so they preserve the index;
* `NumberField.IsOrder.comap_span_singleton_eq_of_sup_eq_top`: if `β𝒪_K` is coprime to `𝔠`
  for `β ∈ O`, then `β𝒪_K ∩ O = βO`.
-/

namespace NumberField.IsOrder

variable {K : Type*} [Field K] [NumberField K] {O : Subalgebra ℤ K}

/-- The conductor lies in the image of the order. -/
private theorem exists_eq_of_mem_conductor (hO : NumberField.IsOrder K O)
    {x : integralClosure ℤ K}
    (hx : x ∈ (O.comap (integralClosure ℤ K).val).conductorIdeal) :
    ∃ o : O, Subalgebra.inclusion hO.le_integralClosure o = x := by
  have h := Subalgebra.mem_conductorIdeal.mp hx 1
  rw [mul_one] at h
  exact ⟨⟨(x : K), h⟩, Subtype.ext rfl⟩

/-- The conductor of `O` is the image of its contraction to `O`. -/
private theorem map_comap_conductor_le (hO : NumberField.IsOrder K O) {x : integralClosure ℤ K}
    (hx : x ∈ (O.comap (integralClosure ℤ K).val).conductorIdeal) :
    ∃ o ∈ ((O.comap (integralClosure ℤ K).val).conductorIdeal).comap
      (Subalgebra.inclusion hO.le_integralClosure),
      Subalgebra.inclusion hO.le_integralClosure o = x := by
  obtain ⟨o, ho⟩ := exists_eq_of_mem_conductor hO hx
  exact ⟨o, Ideal.mem_comap.mpr (ho ▸ hx), ho⟩

/-- An element of `𝔟𝒪_K` times an element of the conductor is the image of an element of `𝔟`
(Conrad: `𝔟𝒪_K𝔠 = 𝔟𝔠 ⊆ 𝔟`). -/
private theorem exists_mem_eq_mul_of_mem_map (hO : NumberField.IsOrder K O) {b : Ideal O}
    {y : integralClosure ℤ K} (hy : y ∈ b.map (Subalgebra.inclusion hO.le_integralClosure))
    {γ : integralClosure ℤ K}
    (hγ : γ ∈ (O.comap (integralClosure ℤ K).val).conductorIdeal) :
    ∃ z ∈ b, Subalgebra.inclusion hO.le_integralClosure z = y * γ := by
  change y ∈ Ideal.span (Subalgebra.inclusion hO.le_integralClosure '' (b : Set O)) at hy
  induction hy using Submodule.span_induction generalizing γ with
  | mem y hy =>
    obtain ⟨β, hβ, rfl⟩ := hy
    obtain ⟨g, rfl⟩ := exists_eq_of_mem_conductor hO hγ
    exact ⟨β * g, b.mul_mem_right g hβ, map_mul _ _ _⟩
  | zero => exact ⟨0, b.zero_mem, by simp⟩
  | add y₁ y₂ _ _ ih₁ ih₂ =>
    obtain ⟨z₁, hz₁, h₁⟩ := ih₁ hγ
    obtain ⟨z₂, hz₂, h₂⟩ := ih₂ hγ
    exact ⟨z₁ + z₂, b.add_mem hz₁ hz₂, by rw [map_add, h₁, h₂, add_mul]⟩
  | smul s y _ ih =>
    obtain ⟨z, hz, h⟩ := ih (Ideal.mul_mem_left _ s hγ)
    exact ⟨z, hz, by rw [h, smul_eq_mul]; ring⟩

/-- **Contraction of an ideal coprime to the conductor.** Let $O$ be an order in a number field
$K$, with conductor $\mathfrak{c} \subseteq \mathcal{O}_K$, and let $\mathfrak{a}$ be an ideal of
$\mathcal{O}_K$ with $\mathfrak{a} + \mathfrak{c} = \mathcal{O}_K$. Then
$(\mathfrak{a} \cap O) + \mathfrak{c} = O$, where $\mathfrak{a} \cap O$ and
$\mathfrak{c} = \mathfrak{c} \cap O$ are the contractions along $O \hookrightarrow \mathcal{O}_K$
(K. Conrad, *The conductor ideal of an order*, Theorem 3.8(1), p. 6, proof p. 7). -/
theorem sup_comap_eq_top_of_sup_eq_top (hO : NumberField.IsOrder K O)
    {a : Ideal (integralClosure ℤ K)}
    (ha : a ⊔ (O.comap (integralClosure ℤ K).val).conductorIdeal = ⊤) :
    a.comap (Subalgebra.inclusion hO.le_integralClosure) ⊔
      ((O.comap (integralClosure ℤ K).val).conductorIdeal).comap
        (Subalgebra.inclusion hO.le_integralClosure) = ⊤ := by
  set ι := Subalgebra.inclusion hO.le_integralClosure
  obtain ⟨α, hα, γ, hγ, hαγ⟩ := Submodule.mem_sup.mp (ha ▸ Submodule.mem_top (x := 1))
  obtain ⟨g, hg, rfl⟩ := map_comap_conductor_le hO hγ
  rw [Ideal.eq_top_iff_one, Submodule.mem_sup]
  refine ⟨1 - g, Ideal.mem_comap.mpr ?_, g, hg, sub_add_cancel 1 g⟩
  rw [map_sub, map_one, ← hαγ, add_sub_cancel_right]
  exact hα

/-- **Extension of a contracted ideal coprime to the conductor.** In the setting of
`NumberField.IsOrder.sup_comap_eq_top_of_sup_eq_top`, $(\mathfrak{a} \cap O)\mathcal{O}_K =
\mathfrak{a}$ (Conrad, proof of Theorem 3.8(3), p. 7). -/
theorem map_comap_eq_of_sup_eq_top (hO : NumberField.IsOrder K O)
    {a : Ideal (integralClosure ℤ K)}
    (ha : a ⊔ (O.comap (integralClosure ℤ K).val).conductorIdeal = ⊤) :
    (a.comap (Subalgebra.inclusion hO.le_integralClosure)).map
      (Subalgebra.inclusion hO.le_integralClosure) = a := by
  set ι := Subalgebra.inclusion hO.le_integralClosure
  refine le_antisymm Ideal.map_comap_le fun x hx => ?_
  obtain ⟨u, hu, g, hg, hug⟩ :=
    Submodule.mem_sup.mp ((hO.sup_comap_eq_top_of_sup_eq_top ha) ▸ Submodule.mem_top (x := 1))
  have hgc : ι g ∈ (O.comap (integralClosure ℤ K).val).conductorIdeal := Ideal.mem_comap.mp hg
  obtain ⟨o, ho⟩ := exists_eq_of_mem_conductor hO (Ideal.mul_mem_left _ x hgc)
  have hoa : o ∈ a.comap ι := Ideal.mem_comap.mpr (ho ▸ Ideal.mul_mem_right _ a hx)
  have hx' : x = x * ι u + ι o := by
    rw [ho, ← mul_add, ← map_add, hug, map_one, mul_one]
  rw [hx']
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ x (Ideal.mem_map_of_mem ι hu))
    (Ideal.mem_map_of_mem ι hoa)

/-- **The residue ring of a contracted ideal coprime to the conductor.** In the setting of
`NumberField.IsOrder.sup_comap_eq_top_of_sup_eq_top`, the natural ring homomorphism
$O/(\mathfrak{a} \cap O) \to \mathcal{O}_K/\mathfrak{a}$ is bijective (Conrad, Theorem 3.8(1),
p. 6, proof p. 7). -/
theorem quotientMap_comap_bijective (hO : NumberField.IsOrder K O)
    {a : Ideal (integralClosure ℤ K)}
    (ha : a ⊔ (O.comap (integralClosure ℤ K).val).conductorIdeal = ⊤) :
    Function.Bijective (Ideal.quotientMap a
      (Subalgebra.inclusion hO.le_integralClosure : O →+* integralClosure ℤ K) le_rfl) := by
  refine ⟨Ideal.quotientMap_injective, fun y => ?_⟩
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨α, hα, γ, hγ, hαγ⟩ := Submodule.mem_sup.mp (ha ▸ Submodule.mem_top (x := 1))
  obtain ⟨o, ho⟩ := exists_eq_of_mem_conductor hO (Ideal.mul_mem_left _ y hγ)
  refine ⟨Ideal.Quotient.mk _ o, ?_⟩
  rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
  have : (Subalgebra.inclusion hO.le_integralClosure : O →+* integralClosure ℤ K) o - y =
      -(y * α) := by
    change Subalgebra.inclusion hO.le_integralClosure o - y = _
    rw [ho]
    linear_combination y * hαγ
  rw [this]
  exact a.neg_mem (Ideal.mul_mem_left _ y hα)

/-- **Extension of an ideal coprime to the conductor.** Let $O$ be an order in a number field
$K$ with conductor $\mathfrak{c}$, and let $\mathfrak{b}$ be an ideal of $O$ with
$\mathfrak{b} + \mathfrak{c} = O$ ($\mathfrak{c}$ contracted to $O$). Then
$\mathfrak{b}\mathcal{O}_K + \mathfrak{c} = \mathcal{O}_K$ (Conrad, Theorem 3.8(2), p. 6, proof
p. 7). -/
theorem map_sup_eq_top_of_sup_eq_top (hO : NumberField.IsOrder K O) {b : Ideal O}
    (hb : b ⊔ ((O.comap (integralClosure ℤ K).val).conductorIdeal).comap
      (Subalgebra.inclusion hO.le_integralClosure) = ⊤) :
    b.map (Subalgebra.inclusion hO.le_integralClosure) ⊔
      (O.comap (integralClosure ℤ K).val).conductorIdeal = ⊤ := by
  set ι := Subalgebra.inclusion hO.le_integralClosure
  obtain ⟨β, hβ, g, hg, hβg⟩ := Submodule.mem_sup.mp (hb ▸ Submodule.mem_top (x := 1))
  rw [Ideal.eq_top_iff_one, Submodule.mem_sup]
  exact ⟨ι β, Ideal.mem_map_of_mem ι hβ, ι g, Ideal.mem_comap.mp hg, by
    rw [← map_add, hβg, map_one]⟩

/-- **Contraction of an extended ideal coprime to the conductor.** In the setting of
`NumberField.IsOrder.map_sup_eq_top_of_sup_eq_top`, $\mathfrak{b}\mathcal{O}_K \cap O =
\mathfrak{b}$ (Conrad, Theorem 3.8(2), proof p. 7). -/
theorem comap_map_eq_of_sup_eq_top (hO : NumberField.IsOrder K O) {b : Ideal O}
    (hb : b ⊔ ((O.comap (integralClosure ℤ K).val).conductorIdeal).comap
      (Subalgebra.inclusion hO.le_integralClosure) = ⊤) :
    (b.map (Subalgebra.inclusion hO.le_integralClosure)).comap
      (Subalgebra.inclusion hO.le_integralClosure) = b := by
  set ι := Subalgebra.inclusion hO.le_integralClosure
  refine le_antisymm (fun x hx => ?_) Ideal.le_comap_map
  obtain ⟨β, hβ, g, hg, hβg⟩ := Submodule.mem_sup.mp (hb ▸ Submodule.mem_top (x := 1))
  obtain ⟨z, hz, hzx⟩ := exists_mem_eq_mul_of_mem_map hO (Ideal.mem_comap.mp hx)
    (Ideal.mem_comap.mp hg)
  have hxg : x * g = z := Subalgebra.inclusion_injective hO.le_integralClosure
    (by rw [map_mul, hzx])
  have hx' : x = x * β + z := by rw [← hxg, ← mul_add, hβg, mul_one]
  rw [hx']
  exact b.add_mem (b.mul_mem_left x hβ) hz

/-- **The residue ring of an ideal coprime to the conductor.** In the setting of
`NumberField.IsOrder.map_sup_eq_top_of_sup_eq_top`, the natural ring homomorphism
$O/\mathfrak{b} \to \mathcal{O}_K/\mathfrak{b}\mathcal{O}_K$ is bijective (Conrad,
Theorem 3.8(2), p. 6, proof p. 7). -/
theorem quotientMap_map_bijective (hO : NumberField.IsOrder K O) {b : Ideal O}
    (hb : b ⊔ ((O.comap (integralClosure ℤ K).val).conductorIdeal).comap
      (Subalgebra.inclusion hO.le_integralClosure) = ⊤) :
    Function.Bijective (Ideal.quotientMap (I := b)
      (b.map (Subalgebra.inclusion hO.le_integralClosure))
      (Subalgebra.inclusion hO.le_integralClosure : O →+* integralClosure ℤ K)
      (by rw [Ideal.comap_coe]; exact Ideal.le_comap_map)) := by
  refine ⟨Ideal.quotientMap_injective' ?_, fun y => ?_⟩
  · rw [Ideal.comap_coe, hO.comap_map_eq_of_sup_eq_top hb]
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  obtain ⟨α, hα, γ, hγ, hαγ⟩ :=
    Submodule.mem_sup.mp ((hO.map_sup_eq_top_of_sup_eq_top hb) ▸ Submodule.mem_top (x := 1))
  obtain ⟨o, ho⟩ := exists_eq_of_mem_conductor hO (Ideal.mul_mem_left _ y hγ)
  refine ⟨Ideal.Quotient.mk _ o, ?_⟩
  rw [Ideal.quotientMap_mk, Ideal.Quotient.eq]
  have : (Subalgebra.inclusion hO.le_integralClosure : O →+* integralClosure ℤ K) o - y =
      -(y * α) := by
    change Subalgebra.inclusion hO.le_integralClosure o - y = _
    rw [ho]
    linear_combination y * hαγ
  rw [this]
  exact neg_mem (Ideal.mul_mem_left _ y hα)

/-- **Contraction is multiplicative on ideals coprime to the conductor.** If $\mathfrak{a}$ and
$\mathfrak{a}'$ are ideals of $\mathcal{O}_K$ coprime to the conductor $\mathfrak{c}$ of an order
$O$, then $(\mathfrak{a} \cap O)(\mathfrak{a}' \cap O) = \mathfrak{a}\mathfrak{a}' \cap O$
(Conrad, Theorem 3.8(3), p. 6, proof p. 7). -/
theorem comap_mul_of_sup_eq_top (hO : NumberField.IsOrder K O)
    {a a' : Ideal (integralClosure ℤ K)}
    (ha : a ⊔ (O.comap (integralClosure ℤ K).val).conductorIdeal = ⊤)
    (ha' : a' ⊔ (O.comap (integralClosure ℤ K).val).conductorIdeal = ⊤) :
    a.comap (Subalgebra.inclusion hO.le_integralClosure) *
        a'.comap (Subalgebra.inclusion hO.le_integralClosure) =
      (a * a').comap (Subalgebra.inclusion hO.le_integralClosure) := by
  set ι := Subalgebra.inclusion hO.le_integralClosure
  have hc : a.comap ι * a'.comap ι ⊔
      ((O.comap (integralClosure ℤ K).val).conductorIdeal).comap ι = ⊤ := by
    rw [← Ideal.isCoprime_iff_sup_eq] at *
    exact IsCoprime.mul_left (Ideal.isCoprime_iff_sup_eq.mpr
      (hO.sup_comap_eq_top_of_sup_eq_top (Ideal.isCoprime_iff_sup_eq.mp ha)))
      (Ideal.isCoprime_iff_sup_eq.mpr
        (hO.sup_comap_eq_top_of_sup_eq_top (Ideal.isCoprime_iff_sup_eq.mp ha')))
  rw [← hO.comap_map_eq_of_sup_eq_top hc, Ideal.map_mul, hO.map_comap_eq_of_sup_eq_top ha,
    hO.map_comap_eq_of_sup_eq_top ha']

/-- **Ideals of an order coprime to the conductor.** Let $K$ be a number field with ring of
integers $\mathcal{O}_K$ (`integralClosure ℤ K`), let $O$ be an order in $K$
(`NumberField.IsOrder`) with inclusion $\iota : O \hookrightarrow \mathcal{O}_K$, and let
$\mathfrak{c} = \{x \in \mathcal{O}_K : x\mathcal{O}_K \subseteq O\}$ be its conductor
(`Subalgebra.conductorIdeal`), an ideal of $\mathcal{O}_K$ contained in $O$. An ideal
$\mathfrak{a}$ of $\mathcal{O}_K$ is coprime to $\mathfrak{c}$ if
$\mathfrak{a} + \mathfrak{c} = \mathcal{O}_K$, and an ideal $\mathfrak{b}$ of $O$ is coprime to
$\mathfrak{c}$ if $\mathfrak{b} + \iota^{-1}(\mathfrak{c}) = O$. Write
$\mathfrak{a} \cap O = \iota^{-1}(\mathfrak{a})$ and $\mathfrak{b}\mathcal{O}_K$ for the ideal of
$\mathcal{O}_K$ generated by $\iota(\mathfrak{b})$. Then:
1. if $\mathfrak{a}$ is coprime to $\mathfrak{c}$, then $\mathfrak{a} \cap O$ is coprime to
   $\mathfrak{c}$, $(\mathfrak{a} \cap O)\mathcal{O}_K = \mathfrak{a}$, and the natural ring
   homomorphism $O/(\mathfrak{a} \cap O) \to \mathcal{O}_K/\mathfrak{a}$ is bijective;
2. if $\mathfrak{b}$ is coprime to $\mathfrak{c}$, then $\mathfrak{b}\mathcal{O}_K$ is coprime
   to $\mathfrak{c}$, $\mathfrak{b}\mathcal{O}_K \cap O = \mathfrak{b}$, and the natural ring
   homomorphism $O/\mathfrak{b} \to \mathcal{O}_K/\mathfrak{b}\mathcal{O}_K$ is bijective;
3. both maps send nonzero ideals to nonzero ideals, so by (1) and (2) they are mutually inverse
   bijections between the nonzero ideals of $\mathcal{O}_K$ coprime to $\mathfrak{c}$ and the
   nonzero ideals of $O$ coprime to $\mathfrak{c}$; and they are multiplicative:
   $(\mathfrak{a} \cap O)(\mathfrak{a}' \cap O) = \mathfrak{a}\mathfrak{a}' \cap O$ for
   $\mathfrak{a}, \mathfrak{a}'$ coprime to $\mathfrak{c}$, and
   $(\mathfrak{b}\mathcal{O}_K)(\mathfrak{b}'\mathcal{O}_K) =
   \mathfrak{b}\mathfrak{b}'\mathcal{O}_K$ for all $\mathfrak{b}, \mathfrak{b}'$.

This is K. Conrad, *The conductor ideal of an order*, Theorem 3.8 (statement p. 6, proof p. 7),
with relatively prime ideals as on p. 4 (§3). The index is preserved:
`NumberField.IsOrder.natCard_quotient_comap_of_sup_eq_top` and
`NumberField.IsOrder.natCard_quotient_map_of_sup_eq_top`. -/
theorem ideals_coprime_conductor (hO : NumberField.IsOrder K O) :
    (∀ a : Ideal (integralClosure ℤ K),
      a ⊔ (O.comap (integralClosure ℤ K).val).conductorIdeal = ⊤ →
        a.comap (Subalgebra.inclusion hO.le_integralClosure) ⊔
            ((O.comap (integralClosure ℤ K).val).conductorIdeal).comap
              (Subalgebra.inclusion hO.le_integralClosure) = ⊤ ∧
          (a.comap (Subalgebra.inclusion hO.le_integralClosure)).map
              (Subalgebra.inclusion hO.le_integralClosure) = a ∧
          Function.Bijective (Ideal.quotientMap a
            (Subalgebra.inclusion hO.le_integralClosure : O →+* integralClosure ℤ K) le_rfl)) ∧
    (∀ b : Ideal O,
      b ⊔ ((O.comap (integralClosure ℤ K).val).conductorIdeal).comap
          (Subalgebra.inclusion hO.le_integralClosure) = ⊤ →
        b.map (Subalgebra.inclusion hO.le_integralClosure) ⊔
            (O.comap (integralClosure ℤ K).val).conductorIdeal = ⊤ ∧
          (b.map (Subalgebra.inclusion hO.le_integralClosure)).comap
              (Subalgebra.inclusion hO.le_integralClosure) = b ∧
          Function.Bijective (Ideal.quotientMap (I := b)
            (b.map (Subalgebra.inclusion hO.le_integralClosure))
            (Subalgebra.inclusion hO.le_integralClosure : O →+* integralClosure ℤ K)
            (by rw [Ideal.comap_coe]; exact Ideal.le_comap_map))) ∧
    (∀ a : Ideal (integralClosure ℤ K),
      a ⊔ (O.comap (integralClosure ℤ K).val).conductorIdeal = ⊤ → a ≠ ⊥ →
        a.comap (Subalgebra.inclusion hO.le_integralClosure) ≠ ⊥) ∧
    (∀ b : Ideal O, b ≠ ⊥ → b.map (Subalgebra.inclusion hO.le_integralClosure) ≠ ⊥) ∧
    (∀ a a' : Ideal (integralClosure ℤ K),
      a ⊔ (O.comap (integralClosure ℤ K).val).conductorIdeal = ⊤ →
      a' ⊔ (O.comap (integralClosure ℤ K).val).conductorIdeal = ⊤ →
        a.comap (Subalgebra.inclusion hO.le_integralClosure) *
            a'.comap (Subalgebra.inclusion hO.le_integralClosure) =
          (a * a').comap (Subalgebra.inclusion hO.le_integralClosure)) ∧
    (∀ b b' : Ideal O,
      b.map (Subalgebra.inclusion hO.le_integralClosure) *
          b'.map (Subalgebra.inclusion hO.le_integralClosure) =
        (b * b').map (Subalgebra.inclusion hO.le_integralClosure)) := by
  refine ⟨fun a ha => ⟨hO.sup_comap_eq_top_of_sup_eq_top ha, hO.map_comap_eq_of_sup_eq_top ha,
      hO.quotientMap_comap_bijective ha⟩,
    fun b hb => ⟨hO.map_sup_eq_top_of_sup_eq_top hb, hO.comap_map_eq_of_sup_eq_top hb,
      hO.quotientMap_map_bijective hb⟩,
    fun a ha ha0 h => ha0 ?_, fun b hb0 h => hb0 ?_,
    fun a a' ha ha' => hO.comap_mul_of_sup_eq_top ha ha',
    fun b b' => (Ideal.map_mul _ b b').symm⟩
  · rw [← hO.map_comap_eq_of_sup_eq_top ha, h, Ideal.map_bot]
  · rw [← Ideal.map_eq_bot_iff_of_injective (Subalgebra.inclusion_injective hO.le_integralClosure)]
    exact h

/-- **Contraction preserves the index.** If $\mathfrak{a}$ is an ideal of $\mathcal{O}_K$
coprime to the conductor of an order $O$, then
$\#(O/(\mathfrak{a} \cap O)) = \#(\mathcal{O}_K/\mathfrak{a})$ (Conrad, Theorem 3.8(1), p. 6). -/
theorem natCard_quotient_comap_of_sup_eq_top (hO : NumberField.IsOrder K O)
    {a : Ideal (integralClosure ℤ K)}
    (ha : a ⊔ (O.comap (integralClosure ℤ K).val).conductorIdeal = ⊤) :
    Nat.card (O ⧸ a.comap (Subalgebra.inclusion hO.le_integralClosure)) =
      Nat.card (integralClosure ℤ K ⧸ a) := by
  rw [← Ideal.comap_coe]
  exact Nat.card_congr (RingEquiv.ofBijective _ (hO.quotientMap_comap_bijective ha)).toEquiv

/-- **Extension preserves the index.** If $\mathfrak{b}$ is an ideal of an order $O$ coprime to
its conductor, then $\#(O/\mathfrak{b}) = \#(\mathcal{O}_K/\mathfrak{b}\mathcal{O}_K)$ (Conrad,
Theorem 3.8(2), p. 6). -/
theorem natCard_quotient_map_of_sup_eq_top (hO : NumberField.IsOrder K O) {b : Ideal O}
    (hb : b ⊔ ((O.comap (integralClosure ℤ K).val).conductorIdeal).comap
      (Subalgebra.inclusion hO.le_integralClosure) = ⊤) :
    Nat.card (O ⧸ b) =
      Nat.card (integralClosure ℤ K ⧸ b.map (Subalgebra.inclusion hO.le_integralClosure)) :=
  Nat.card_congr (RingEquiv.ofBijective _ (hO.quotientMap_map_bijective hb)).toEquiv

/-- **Principal ideals coprime to the conductor of an order.** Let $K$ be a number field with
ring of integers $\mathcal{O}_K$ (`integralClosure ℤ K`), let $O$ be an order in $K$
(`NumberField.IsOrder`) with inclusion $\iota : O \hookrightarrow \mathcal{O}_K$, and let
$\mathfrak{c} = \{x \in \mathcal{O}_K : x\mathcal{O}_K \subseteq O\}$ be its conductor. If
$\beta \in O$ and $\beta\mathcal{O}_K + \mathfrak{c} = \mathcal{O}_K$, then
$\beta\mathcal{O}_K \cap O = \beta O$, that is, $\iota^{-1}(\iota(\beta)\mathcal{O}_K) =
\beta O$.

This is K. Conrad, *The conductor ideal of an order*, Corollary 3.10 with its proof (p. 7): the
indices $[O : \beta\mathcal{O}_K \cap O]$ and $[\mathcal{O}_K : \beta\mathcal{O}_K]$ agree by
Theorem 3.8, and both $[\mathcal{O}_K : \beta\mathcal{O}_K]$ and $[O : \beta O]$ equal
$|N_{K/\mathbb{Q}}(\beta)|$ (`NumberField.IsOrder.natCard_quotient_span_singleton_eq_abs_norm`;
Conrad, footnote 4, p. 14). For $\beta = 0$ both sides are $0$. -/
theorem comap_span_singleton_eq_of_sup_eq_top (hO : NumberField.IsOrder K O) {β : O}
    (hβ : Ideal.span {Subalgebra.inclusion hO.le_integralClosure β} ⊔
      (O.comap (integralClosure ℤ K).val).conductorIdeal = ⊤) :
    (Ideal.span {Subalgebra.inclusion hO.le_integralClosure β}).comap
      (Subalgebra.inclusion hO.le_integralClosure) = Ideal.span {β} := by
  set ι := Subalgebra.inclusion hO.le_integralClosure with hι
  by_cases hβ0 : β = 0
  · rw [hβ0, map_zero, Ideal.span_singleton_eq_bot.mpr rfl,
      Ideal.comap_bot_of_injective ι (Subalgebra.inclusion_injective hO.le_integralClosure),
      Ideal.span_singleton_eq_bot.mpr rfl]
  have hιβ0 : ι β ≠ 0 := by
    intro h
    apply hβ0
    apply Subalgebra.inclusion_injective hO.le_integralClosure
    rw [map_zero]
    exact h
  have hle : Ideal.span {β} ≤ (Ideal.span {ι β}).comap ι :=
    (Ideal.span_singleton_le_iff_mem _).mpr
      (Ideal.mem_comap.mpr (Ideal.mem_span_singleton_self _))
  have hcard : Nat.card (O ⧸ (Ideal.span {ι β}).comap ι) = Nat.card (O ⧸ Ideal.span {β}) := by
    rw [hO.natCard_quotient_comap_of_sup_eq_top hβ]
    have h1 := (NumberField.isOrder_integralClosure K).natCard_quotient_span_singleton_eq_abs_norm
      hιβ0
    have h2 := hO.natCard_quotient_span_singleton_eq_abs_norm hβ0
    have hval : ((ι β : integralClosure ℤ K) : K) = (β : K) := rfl
    rw [hval] at h1
    exact_mod_cast h1.trans h2.symm
  refine (eq_of_le_of_not_lt hle fun hlt => ?_).symm
  have hfin := hO.finite_quotient (b := Ideal.span {β}) (by
    rwa [Ne, Ideal.span_singleton_eq_bot])
  have hne : Nat.card (O ⧸ Ideal.span {β}) ≠ 0 := Nat.card_ne_zero.mpr ⟨inferInstance, hfin⟩
  have : (Ideal.span {β}).toAddSubgroup.FiniteIndex := ⟨hne⟩
  have hlt' : Nat.card (O ⧸ (Ideal.span {ι β}).comap ι) < Nat.card (O ⧸ Ideal.span {β}) := by
    rw [← Submodule.cardQuot_apply, ← Submodule.cardQuot_apply]
    exact AddSubgroup.index_strictAnti (Submodule.toAddSubgroup_strictMono hlt)
  omega

end NumberField.IsOrder

end
