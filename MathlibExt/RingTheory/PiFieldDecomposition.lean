/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- MathlibExt/RingTheory/PiFieldDecomposition.lean
module

public import MathlibExt.RingTheory.PiFieldQuotient

/-!
# Uniqueness of finite products of fields up to permutation

Let `K` be a field and `F : ι → Type*`, `G : κ → Type*` finite families of fields
with `K`-algebra structures. Any `K`-algebra equivalence between the products
`(∀ i, F i)` and `(∀ j, G j)` induces a permutation of the index types, unique up
to the evident relabelling, together with factorwise `K`-algebra equivalences:
there is `σ : ι ≃ κ` such that `F i ≃ₐ[K] G (σ i)` for every `i`.

The proof goes through one field at a time: a surjective algebra map from a
finite product of fields to a field factors through exactly one coordinate
(`PiFieldQuotient.exists_algEquiv_restrict` plus a singleton-support argument),
and applying this to each coordinate in both directions yields inverse index
maps whose composites are the identity.

This is the corrected form of ATLAS `NumberTheoryI` target N83, Corollary 4.33.
At atlas-lean revision `e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`,
the [English target is lines 521--525 of `v1/Atlas/NumberTheoryI/targets.yaml`](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/targets.yaml#L521-L525),
and the primary Lean source is
[`EtaleAlgebra.etale_decomposition_unique` in
`v1/Atlas/NumberTheoryI/code/EtaleAlgebrasProps.lean`, lines 180--188](https://github.com/facebookresearch/atlas-lean/blob/e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6/v1/Atlas/NumberTheoryI/code/EtaleAlgebrasProps.lean#L180-L188).
Given an equivalence between
`∏ i, F i` and `∏ j, G j`, that theorem concludes only mutual coverage:
every `F i` is equivalent to some `G j`, and every `G j` to some `F i`.
Those two choices need not be inverse and therefore do not retain factor
multiplicities; for example, families of one and two identical rational factors
satisfy that conclusion even though their index types are not equivalent.

Corollary 4.33 says uniqueness *up to permutation and isomorphism of factors*.
Accordingly, `exists_indexEquiv_algEquiv` retains the same product-algebra
equivalence hypothesis but strengthens the source conclusion to one equivalence
`σ : ι ≃ κ` together with aligned factor equivalences
`F i ≃ₐ[K] G (σ i)`. This records multiplicity and supplies the alignment needed
by downstream N266. The `[Finite]` hypotheses merely avoid exposing choices of
enumeration or decidable equality; the proof makes those choices internally.
-/

universe u v w x y

@[expose] public section

namespace PiFieldQuotient

/-- Evaluation at a coordinate is a surjective algebra map. -/
private theorem evalAlgHom_surjective {K : Type*} [Field K] {ι : Type*}
    {F : ι → Type*} [∀ i, Field (F i)] [∀ i, Algebra K (F i)] (i : ι) :
    Function.Surjective (Pi.evalAlgHom K F i) := by
  classical
  intro y
  exact ⟨Pi.single i y, by simpa only [Pi.evalAlgHom_apply] using Pi.single_eq_same i y⟩

/-- The product over a singleton index type is algebra-equivalent to its only factor. -/
private noncomputable def singletonEquiv {K : Type*} [Field K] {ι : Type*}
    {F : ι → Type*} [∀ i, Semiring (F i)] [∀ i, Algebra K (F i)]
    (S : Finset ι) (s0 : S) (hsing : ∀ s : S, s = s0) :
    (∀ s : S, F (s : ι)) ≃ₐ[K] F ((s0 : S) : ι) :=
  { toFun := fun f => f s0
    invFun := fun x s => hsing s ▸ x
    left_inv := fun f => by ext s; rw [hsing s]
    right_inv := fun x => by rfl
    map_mul' := fun _ _ => by rfl
    map_add' := fun _ _ => by rfl
    commutes' := fun _ => by rfl }

/-- A surjective algebra map from a finite product of fields to a field factors
through exactly one coordinate. -/
private theorem exists_factor_of_surjective {K : Type*} [Field K] {ι : Type*}
    [Finite ι] {F : ι → Type*} [∀ i, Field (F i)] [∀ i, Algebra K (F i)]
    {E : Type*} [Field E] [Algebra K E]
    (φ : (∀ i, F i) →ₐ[K] E) (hφ : Function.Surjective φ) :
    ∃ i : ι, ∃ e : F i ≃ₐ[K] E, ∀ x, e (x i) = φ x := by
  classical
  obtain ⟨S, a, ha⟩ := exists_algEquiv_restrict φ hφ
  have hcoord : ∀ (x : ∀ i, F i) (s : S), a (φ x) s = x (s : ι) := by
    intro x s
    have h := congrArg (fun ψ : (∀ i, F i) →ₐ[K] (∀ s : S, F (s : ι)) => ψ x s) ha
    simpa only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom, AlgHom.pi_apply,
      Pi.evalAlgHom_apply] using h
  have hne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have h10 : (1 : ∀ s : S, F (s : ι)) = 0 := by
      ext s
      have hmemEmpty : s.val ∈ (∅ : Finset ι) := by
        rw [← h]
        exact s.property
      exact absurd hmemEmpty (Finset.notMem_empty _)
    have hE : (1 : E) = 0 := by
      have h2 := congrArg (fun y => a.symm y) h10
      simp at h2
    exact one_ne_zero hE
  have hsub : ∀ s₁ s₂ : S, s₁ = s₂ := by
    intro s₁ s₂
    by_contra hne12
    have hne1 : (Pi.single s₁ (1 : F (s₁ : ι)) : ∀ s : S, F (s : ι)) ≠ 0 := by
      intro h
      have h1 := congrArg (fun y : (∀ s : S, F (s : ι)) => y s₁) h
      simp only [Pi.single_eq_same, Pi.zero_apply] at h1
      exact one_ne_zero h1
    have hne2 : (Pi.single s₂ (1 : F (s₂ : ι)) : ∀ s : S, F (s : ι)) ≠ 0 := by
      intro h
      have h1 := congrArg (fun y : (∀ s : S, F (s : ι)) => y s₂) h
      simp only [Pi.single_eq_same, Pi.zero_apply] at h1
      exact one_ne_zero h1
    have hu1 : a.symm (Pi.single s₁ (1 : F (s₁ : ι))) ≠ 0 := by
      intro h
      apply hne1
      have h2 := congrArg ⇑a h
      simpa only [AlgEquiv.apply_symm_apply, map_zero] using h2
    have hu2 : a.symm (Pi.single s₂ (1 : F (s₂ : ι))) ≠ 0 := by
      intro h
      apply hne2
      have h2 := congrArg ⇑a h
      simpa only [AlgEquiv.apply_symm_apply, map_zero] using h2
    have hprod : (Pi.single s₁ (1 : F (s₁ : ι)) * Pi.single s₂ (1 : F (s₂ : ι)) :
        ∀ s : S, F (s : ι)) = 0 := by
      ext t
      by_cases ht : t = s₁
      · subst ht
        simp only [Pi.mul_apply, Pi.single_eq_same,
          Pi.single_eq_of_ne hne12 _, mul_zero, Pi.zero_apply]
      · simp only [Pi.mul_apply, Pi.single_eq_of_ne ht _, zero_mul,
          Pi.zero_apply]
    have hmul : a.symm (Pi.single s₁ (1 : F (s₁ : ι))) *
        a.symm (Pi.single s₂ (1 : F (s₂ : ι))) = 0 := by
      rw [← map_mul, hprod, map_zero]
    exact (mul_ne_zero hu1 hu2) hmul
  obtain ⟨x₀, hx₀⟩ := hne
  let s0 : S := ⟨x₀, hx₀⟩
  refine ⟨s0.val, (a.trans (singletonEquiv S s0 (fun s => hsub s s0))).symm, fun x => ?_⟩
  apply (a.trans (singletonEquiv S s0 (fun s => hsub s s0))).injective
  simp only [AlgEquiv.apply_symm_apply, AlgEquiv.trans_apply]
  exact (hcoord x s0).symm

/-- **Uniqueness of a finite product of fields up to permutation.** Let $K$ be a field, and let
$(F_i)_{i \in I}$ and $(G_j)_{j \in J}$ be families of fields that are $K$-algebras, indexed by
finite types $I$ and $J$. If $e : \prod_{i \in I} F_i \to \prod_{j \in J} G_j$ is an isomorphism
of $K$-algebras, then there is a bijection $\sigma : I \to J$ such that $F_i$ is isomorphic to
$G_{\sigma(i)}$ as a $K$-algebra for every $i \in I$.

Source: ATLAS N83, Corollary 4.33. This is the multiplicity-preserving correction of
`EtaleAlgebra.etale_decomposition_unique` from the primary Lean source. -/
public theorem exists_indexEquiv_algEquiv
    {K : Type u} [Field K]
    {ι : Type v} [Finite ι] {κ : Type w} [Finite κ]
    {F : ι → Type x} [∀ i, Field (F i)] [∀ i, Algebra K (F i)]
    {G : κ → Type y} [∀ j, Field (G j)] [∀ j, Algebra K (G j)]
    (e : (∀ i, F i) ≃ₐ[K] (∀ j, G j)) :
    ∃ σ : ι ≃ κ, ∀ i, Nonempty (F i ≃ₐ[K] G (σ i)) := by
  classical
  have he : Function.Surjective (e.toAlgHom) := by
    intro y
    exact ⟨e.symm y, AlgEquiv.apply_symm_apply e y⟩
  have heSymm : Function.Surjective (e.symm.toAlgHom) := by
    intro y
    exact ⟨e y, AlgEquiv.symm_apply_apply e y⟩
  have hf : ∀ j : κ, ∃ i : ι, ∃ ef : F i ≃ₐ[K] G j, ∀ x, ef (x i) = e x j := by
    intro j
    exact exists_factor_of_surjective ((Pi.evalAlgHom K G j).comp e.toAlgHom)
      ((evalAlgHom_surjective (K := K) (F := G) j).comp he)
  have hg : ∀ i : ι, ∃ k : κ, ∃ eg : G k ≃ₐ[K] F i, ∀ y, eg (y k) = e.symm y i := by
    intro i
    exact exists_factor_of_surjective ((Pi.evalAlgHom K F i).comp e.symm.toAlgHom)
      ((evalAlgHom_surjective (K := K) (F := F) i).comp heSymm)
  choose f ef hf' using hf
  choose g eg hg' using hg
  have hgf : ∀ j : κ, g (f j) = j := by
    intro j
    by_contra hne
    have h0 : (Pi.single j (1 : G j)) (g (f j)) = 0 := Pi.single_eq_of_ne hne _
    have h1 : e.symm (Pi.single j (1 : G j)) (f j) = 0 := by
      have h := hg' (f j) (Pi.single j (1 : G j))
      rw [h0, map_zero] at h
      exact h.symm
    have h2 := hf' j (e.symm (Pi.single j (1 : G j)))
    rw [AlgEquiv.apply_symm_apply] at h2
    rw [h1, map_zero, Pi.single_eq_same] at h2
    exact zero_ne_one h2
  have hfg : ∀ i : ι, f (g i) = i := by
    intro i
    by_contra hne
    have h0 : (Pi.single i (1 : F i)) (f (g i)) = 0 := Pi.single_eq_of_ne hne _
    have h1 : e (Pi.single i (1 : F i)) (g i) = 0 := by
      have h := hf' (g i) (Pi.single i (1 : F i))
      rw [h0, map_zero] at h
      exact h.symm
    have h2 := hg' i (e (Pi.single i (1 : F i)))
    rw [AlgEquiv.symm_apply_apply] at h2
    rw [h1, map_zero, Pi.single_eq_same] at h2
    exact zero_ne_one h2
  exact ⟨Equiv.mk g f (fun i => hfg i) (fun j => hgf j), fun i => ⟨(eg i).symm⟩⟩

end PiFieldQuotient
