/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
-/

/-
Adapted from:

`Theorems/Thm_ClassFunction_exists_trace_eq_sum_induced_linearCharacter_of_
normal_comm_of_pow_prime_pow_mem.lean`
and
`P2M/Sol/S_ClassFunction_exists_trace_eq_sum_induced_linearCharacter_of_
normal_comm_of_pow_prime_pow_mem.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
Adaptations copyright (c) Meta Platforms, Inc. and affiliates, under the
license in the root LICENSE file.
-/

module

public import MathlibExt.RepresentationTheory.ClassFunctionInduced
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.RepresentationTheory.Basic
import Mathlib.Algebra.DirectSum.LinearMap
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.GroupTheory.PGroup
import Mathlib.LinearAlgebra.Eigenspace.Pi
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Trace

/-!
# Monomial characters over an abelian normal subgroup with `p`-group quotient

Let `G` be a finite group with an abelian normal subgroup `A` such that every element of `G`
has a `p`-power in `A`, i.e. `G ⧸ A` is a `p`-group. Then the character of every complex
representation `ρ : G →* GL (Fin n) ℂ` is a sum of characters induced from linear characters
`ψ i : H i →* ℂˣ` of subgroups `H i`.

The proof is by induction on `|G| + dim V`. If `ρ(G)` is abelian, the representation splits
into common eigenspaces. Otherwise, there is a normal subgroup `B ≥ A` whose image `ρ(B)` is
abelian but not contained in the center of `ρ(G)` (`B` itself need not be abelian), and `V`
decomposes into weight spaces for `B`, permuted by `G`. If the action on the weights with
nonzero weight space is not transitive, `V` splits into two proper subrepresentations; if it
is transitive, `V` is induced from a weight space of the stabilizer of a weight, a proper
subgroup.

## Main result

* `ClassFunction.exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem`
-/

@[expose] public section

noncomputable section

universe u v w

open Module

namespace ClassFunction

namespace MonomialProof

section Bookkeeping

variable {K : Type u} [Group K] [Fintype K]

open scoped Classical in
private def extChar (L : Subgroup K) (ψ : L →* ℂˣ) : K → ℂ :=
  fun x => if hx : x ∈ L then ((ψ ⟨x, hx⟩ : ℂˣ) : ℂ) else 0

private abbrev Entry (K : Type u) [Group K] := Σ L : Subgroup K, (L →* ℂˣ)

private def val (e : Entry K) : K → ℂ := ClassFunction.induced e.1 (extChar e.1 e.2)

private def lsum (l : List (Entry K)) : K → ℂ := fun g => (l.map fun e => val e g).sum

private theorem lsum_nil : lsum ([] : List (Entry K)) = 0 := by
  funext g; simp [lsum]

private theorem lsum_cons (e : Entry K) (l : List (Entry K)) : lsum (e :: l) = val e + lsum l := by
  funext g; simp [lsum]

private theorem lsum_append (l₁ l₂ : List (Entry K)) : lsum (l₁ ++ l₂) = lsum l₁ + lsum l₂ := by
  funext g; simp [lsum, List.sum_append]

private theorem lsum_replicate (n : ℕ) (e : Entry K) (g : K) :
    lsum (List.replicate n e) g = (n : ℂ) * val e g := by
  induction n with
  | zero => simp [lsum]
  | succ n ih =>
    rw [List.replicate_succ, lsum_cons, Pi.add_apply, ih]
    push_cast
    ring

private theorem lsum_flatten_replicate {X : Type*} (L : List X) (n : X → ℕ) (e : X → Entry K)
    (g : K) :
    lsum ((L.map fun x => List.replicate (n x) (e x)).flatten) g =
      (L.map fun x => (n x : ℂ) * val (e x) g).sum := by
  induction L with
  | nil => simp [lsum]
  | cons x L ih =>
    rw [List.map_cons, List.flatten_cons, lsum_append, Pi.add_apply, ih, lsum_replicate,
      List.map_cons, List.sum_cons]

private def lift (H : Subgroup K) (e : Entry H) : Entry K :=
  ⟨e.1.map H.subtype,
    e.2.comp (e.1.equivMapOfInjective H.subtype H.subtype_injective).symm.toMonoidHom⟩

omit [Fintype K] in
private theorem lift_snd_apply (H : Subgroup K) (e : Entry H) (x : (lift H e).1) :
    (lift H e).2 x = e.2 ((e.1.equivMapOfInjective H.subtype H.subtype_injective).symm x) := rfl

open scoped Classical in
omit [Fintype K] in
private theorem extChar_lift (H : Subgroup K) (e : Entry H) (g : K) (hg : g ∈ e.1.map H.subtype) :
    extChar (lift H e).1 (lift H e).2 g = if hg' : g ∈ H then extChar e.1 e.2 ⟨g, hg'⟩ else 0 := by
  obtain ⟨z, hz, rfl⟩ := hg
  simp only [Subgroup.coe_subtype, SetLike.coe_mem, ↓reduceDIte]
  have hz' : (⟨(z : K), z.2⟩ : H) ∈ e.1 := by simpa using hz
  have hmem : (z : K) ∈ (lift H e).1 := ⟨z, hz, rfl⟩
  simp only [extChar, dite_eq_left hz', dite_eq_left hmem, lift_snd_apply]
  congr 2
  apply (e.1.equivMapOfInjective H.subtype H.subtype_injective).injective
  exact (MulEquiv.apply_symm_apply _ _).trans (Subtype.ext rfl)

open scoped Classical in
private theorem val_lift (H : Subgroup K) (e : Entry H) :
    val (lift H e) =
      ClassFunction.induced H (fun g => if hg : g ∈ H then val e ⟨g, hg⟩ else 0) := by
  rw [val]
  unfold val
  rw [ClassFunction.induced_induced H e.1 (extChar e.1 e.2)]
  apply ClassFunction.induced_congr
  intro g hg
  exact extChar_lift H e g hg

open scoped Classical in
private theorem induced_lsum_eq (H : Subgroup K) (l : List (Entry H)) :
    ClassFunction.induced H (fun g => if hg : g ∈ H then lsum l ⟨g, hg⟩ else 0) =
      lsum (l.map (lift H)) := by
  induction l with
  | nil =>
    rw [List.map_nil, lsum_nil, lsum_nil]
    have : (fun g : K => if hg : g ∈ H then (0 : H → ℂ) ⟨g, hg⟩ else 0) = 0 := by
      funext g; split_ifs <;> rfl
    rw [this, ClassFunction.induced_zero]
  | cons e l ih =>
    rw [List.map_cons, lsum_cons, lsum_cons, val_lift, ← ih, ← ClassFunction.induced_add]
    apply ClassFunction.induced_congr
    intro g hg
    simp only [Pi.add_apply, dite_eq_left hg]

end Bookkeeping

section Rep

variable {K : Type u} [Group K] [Fintype K]
variable {W : Type v} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
variable (σ : Representation ℂ K W)

omit [Fintype K] [FiniteDimensional ℂ W] in
private theorem isSemisimple [Finite K] (k : K) : Module.End.IsSemisimple (σ k) := by
  have := Fintype.ofFinite K
  apply Module.End.isSemisimple_of_squarefree_aeval_eq_zero
    (p := Polynomial.X ^ Fintype.card K - Polynomial.C 1)
  · exact (Polynomial.separable_X_pow_sub_C (1 : ℂ) (by exact_mod_cast Fintype.card_ne_zero)
      one_ne_zero).squarefree
  · rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, map_one, ← map_pow,
      pow_card_eq_one, map_one, sub_self]

omit [Fintype K] [FiniteDimensional ℂ W] in
private theorem maxGenEigenspace_eq [Finite K] (k : K) (μ : ℂ) :
    Module.End.maxGenEigenspace (σ k) μ = Module.End.eigenspace (σ k) μ :=
  (isSemisimple σ k).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace μ

private def act (k : K) : W ≃ₗ[ℂ] W :=
  { σ k with
    invFun := σ k⁻¹
    left_inv := fun v => by
      change (σ k⁻¹ * σ k) v = v
      rw [← map_mul, inv_mul_cancel, map_one]; rfl
    right_inv := fun v => by
      change (σ k * σ k⁻¹) v = v
      rw [← map_mul, mul_inv_cancel, map_one]; rfl }

omit [Fintype K] [FiniteDimensional ℂ W] in
@[local simp] private theorem act_apply (k : K) (v : W) : act σ k v = σ k v := rfl

omit [Fintype K] [FiniteDimensional ℂ W] in
private theorem act_symm_apply (k : K) (v : W) : (act σ k).symm v = σ k⁻¹ v := rfl

omit [Fintype K] [FiniteDimensional ℂ W] in
private theorem trace_conj (x g : K) :
    LinearMap.trace ℂ W (σ (x⁻¹ * g * x)) = LinearMap.trace ℂ W (σ g) := by
  rw [σ.map_mul, σ.map_mul, LinearMap.trace_mul_cycle, ← σ.map_mul, ← σ.map_mul, mul_inv_cancel,
    one_mul]

variable (A : Subgroup K)

private def wt (χ : A → ℂ) : Submodule ℂ W := ⨅ a : A, Module.End.maxGenEigenspace (σ a) (χ a)

omit [Fintype K] [FiniteDimensional ℂ W] in
private theorem mem_wt [Finite K] (χ : A → ℂ) (v : W) :
    v ∈ wt σ A χ ↔ ∀ a : A, σ a v = χ a • v := by
  simp only [wt, Submodule.mem_iInf, maxGenEigenspace_eq, Module.End.mem_eigenspace_iff]

variable (hcomm : ∀ a b : A, σ a * σ b = σ b * σ a)
include hcomm

open scoped Classical in
private theorem isInternal_wt : DirectSum.IsInternal (wt σ A) := by
  have h1 : Pairwise fun a b : A => Commute (σ a) (σ b) := fun a b _ => hcomm a b
  have htop :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_iSup_maxGenEigenspace_eq_top_of_commute
    (fun a : A => (σ a : Module.End ℂ W)) h1
    (fun a => Module.End.iSup_maxGenEigenspace_eq_top _)
  have hind := Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo
    (fun a : A => (σ a : Module.End ℂ W))
    (fun a b φ => Module.End.mapsTo_maxGenEigenspace_of_comm (hcomm b a) φ)
  exact DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop

omit hcomm [Fintype K] [FiniteDimensional ℂ W] in
private theorem mapsTo_wt_of_comm [Finite K] (χ : A → ℂ) (f : W →ₗ[ℂ] W)
    (hf : ∀ a : A, f * σ a = σ a * f) :
    Set.MapsTo f (wt σ A χ) (wt σ A χ) := by
  intro v hv
  rw [SetLike.mem_coe, mem_wt] at hv ⊢
  intro a
  have := congrArg (fun T => T v) (hf a)
  simp only [mul_apply_eq_comp] at this
  rw [← this, hv a, map_smul]

open scoped Classical in
omit hcomm in
private theorem finite_wt (h : DirectSum.IsInternal (wt σ A)) : {χ : A → ℂ | wt σ A χ ≠ ⊥}.Finite :=
  WellFoundedGT.finite_ne_bot_of_iSupIndep h.submodule_iSupIndep

omit hcomm

omit [Fintype K] [FiniteDimensional ℂ W] in
private theorem exists_ne_zero_of_ne_bot {χ : A → ℂ} (hχ : wt σ A χ ≠ ⊥) :
    ∃ v ∈ wt σ A χ, v ≠ 0 := by
  by_contra h
  push Not at h
  exact hχ ((Submodule.eq_bot_iff _).2 h)

omit [Fintype K] [FiniteDimensional ℂ W] in
private theorem weight_mul [Finite K] {χ : A → ℂ} (hχ : wt σ A χ ≠ ⊥) (a b : A) :
    χ (a * b) = χ a * χ b := by
  obtain ⟨v, hv, hv0⟩ := exists_ne_zero_of_ne_bot σ A hχ
  rw [mem_wt] at hv
  have h1 : σ (a * b : A) v = χ (a * b) • v := hv (a * b)
  have h2 : σ (a * b : A) v = (χ a * χ b) • v := by
    rw [Subgroup.coe_mul, map_mul, mul_apply_eq_comp, hv b, map_smul, hv a, smul_smul, mul_comm]
  have := h1.symm.trans h2
  rw [← sub_eq_zero, ← sub_smul, smul_eq_zero] at this
  rcases this with h | h
  · exact sub_eq_zero.1 h
  · exact absurd h hv0

omit [Fintype K] [FiniteDimensional ℂ W] in
private theorem weight_one [Finite K] {χ : A → ℂ} (hχ : wt σ A χ ≠ ⊥) : χ 1 = 1 := by
  obtain ⟨v, hv, hv0⟩ := exists_ne_zero_of_ne_bot σ A hχ
  rw [mem_wt] at hv
  have h1 : σ (1 : A) v = χ 1 • v := hv 1
  rw [Subgroup.coe_one, map_one, one_apply_eq_self] at h1
  have : (χ 1 - 1) • v = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
  rw [smul_eq_zero] at this
  rcases this with h | h
  · exact (sub_eq_zero.1 h)
  · exact absurd h hv0

omit [Fintype K] [FiniteDimensional ℂ W] in
private theorem weight_ne_zero [Finite K] {χ : A → ℂ} (hχ : wt σ A χ ≠ ⊥) (a : A) : χ a ≠ 0 := by
  intro h
  have := weight_mul σ A hχ a⁻¹ a
  rw [inv_mul_cancel, weight_one σ A hχ, h, mul_zero] at this
  exact one_ne_zero this

private def weightHom {χ : A → ℂ} (hχ : wt σ A χ ≠ ⊥) : A →* ℂˣ where
  toFun a := Units.mk0 (χ a) (weight_ne_zero σ A hχ a)
  map_one' := Units.ext (weight_one σ A hχ)
  map_mul' a b := Units.ext (weight_mul σ A hχ a b)

omit [FiniteDimensional ℂ W] in
@[local simp] private theorem weightHom_apply {χ : A → ℂ} (hχ : wt σ A χ ≠ ⊥) (a : A) :
    ((weightHom σ A hχ a : ℂˣ) : ℂ) = χ a := rfl

variable [hA : A.Normal]

private scoped instance weightAction : MulAction K (A → ℂ) where
  smul k χ := fun a => χ ⟨k⁻¹ * a * k, hA.conj_mem' a a.2 k⟩
  one_smul χ := by
    funext a
    change χ ⟨1⁻¹ * a * 1, _⟩ = χ a
    congr 1
    apply Subtype.ext
    simp
  mul_smul k₁ k₂ χ := by
    funext a
    change χ ⟨(k₁ * k₂)⁻¹ * a * (k₁ * k₂), _⟩ = χ ⟨k₂⁻¹ * (k₁⁻¹ * a * k₁ : K) * k₂, _⟩
    congr 1
    apply Subtype.ext
    simp only [mul_inv_rev]
    group

omit [Fintype K] in
private theorem smul_weight_apply (k : K) (χ : A → ℂ) (a : A) :
    (k • χ) a = χ ⟨k⁻¹ * a * k, hA.conj_mem' a a.2 k⟩ := rfl

omit [Fintype K] [FiniteDimensional ℂ W] in
private theorem mapsTo_smul [Finite K] (k : K) (χ : A → ℂ) :
    Set.MapsTo (σ k) (wt σ A χ) (wt σ A (k • χ)) := by
  intro v hv
  rw [SetLike.mem_coe, mem_wt] at hv ⊢
  intro a
  rw [smul_weight_apply]
  have e : (a : K) = k * (k⁻¹ * a * k) * k⁻¹ := by group
  have : σ a (σ k v) = σ k (σ (⟨k⁻¹ * a * k, hA.conj_mem' a a.2 k⟩ : A) v) := by
    change (σ a * σ k) v = (σ k * σ (k⁻¹ * a * k)) v
    rw [← map_mul, ← map_mul]
    congr 2
    group
  rw [this, hv, map_smul]

omit [Fintype K] [FiniteDimensional ℂ W] in
private theorem map_wt_eq [Finite K] (k : K) (χ : A → ℂ) :
    (wt σ A χ).map (act σ k : W →ₗ[ℂ] W) = wt σ A (k • χ) := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact mapsTo_smul σ A k χ hv
  · intro v hv
    refine ⟨σ k⁻¹ v, ?_, ?_⟩
    · have := mapsTo_smul σ A k⁻¹ (k • χ) hv
      rwa [smul_smul, inv_mul_cancel, one_smul] at this
    · change σ k (σ k⁻¹ v) = v
      rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one, one_apply_eq_self]

private def wtEquiv (k : K) (χ : A → ℂ) : wt σ A χ ≃ₗ[ℂ] wt σ A (k • χ) :=
  LinearEquiv.ofSubmodules (act σ k) _ _ (map_wt_eq σ A k χ)

omit [FiniteDimensional ℂ W] in
private theorem wtEquiv_apply (k : K) (χ : A → ℂ) (v : wt σ A χ) :
    ((wtEquiv σ A k χ v : wt σ A (k • χ)) : W) = σ k v := rfl

omit [FiniteDimensional ℂ W] in
private theorem wtEquiv_symm_apply (k : K) (χ : A → ℂ) (v : wt σ A (k • χ)) :
    (((wtEquiv σ A k χ).symm v : wt σ A χ) : W) = σ k⁻¹ v := rfl

omit [Fintype K] [FiniteDimensional ℂ W] in
private theorem wt_smul_ne_bot_iff [Finite K] (k : K) (χ : A → ℂ) :
    wt σ A (k • χ) ≠ ⊥ ↔ wt σ A χ ≠ ⊥ := by
  rw [← map_wt_eq]
  exact not_congr ((Submodule.map_injective_of_injective (act σ k).injective).eq_iff'
    (Submodule.map_bot _))

omit [Fintype K] [FiniteDimensional ℂ W] in
private theorem trace_restrict_conj [Finite K] (k g : K) (χ : A → ℂ)
    (hg : Set.MapsTo (σ (k⁻¹ * g * k)) (wt σ A χ) (wt σ A χ))
    (hg' : Set.MapsTo (σ g) (wt σ A (k • χ)) (wt σ A (k • χ))) :
    LinearMap.trace ℂ _ ((σ g).restrict hg') =
      LinearMap.trace ℂ _ ((σ (k⁻¹ * g * k)).restrict hg) := by
  have := Fintype.ofFinite K
  have : (σ g).restrict hg' = (wtEquiv σ A k χ).conj ((σ (k⁻¹ * g * k)).restrict hg) := by
    apply LinearMap.ext
    intro v
    apply Subtype.ext
    rw [LinearEquiv.conj_apply]
    simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      wtEquiv_apply]
    change σ g v = σ k (σ (k⁻¹ * g * k) (((wtEquiv σ A k χ).symm v : wt σ A χ) : W))
    rw [wtEquiv_symm_apply, ← mul_apply_eq_comp, ← mul_apply_eq_comp, ← map_mul, ← map_mul]
    congr 2
    group
  rw [this, LinearMap.trace_conj']

omit [Fintype K] [FiniteDimensional ℂ W] in
private theorem mapsTo_of_smul_eq [Finite K] {χ : A → ℂ} {h : K} (hh : h • χ = χ) :
    Set.MapsTo (σ h) (wt σ A χ) (wt σ A χ) := by
  have := mapsTo_smul σ A h χ
  rwa [hh] at this

private def stabRep (χ : A → ℂ) (H₁ : Subgroup K) (hH₁ : ∀ h ∈ H₁, h • χ = χ) :
    Representation ℂ H₁ (wt σ A χ) :=
  Representation.subrepresentation (σ.comp H₁.subtype) (wt σ A χ)
    (fun h _ hv => mapsTo_of_smul_eq σ A (hH₁ h h.2) hv)

omit [FiniteDimensional ℂ W] in
private theorem stabRep_apply (χ : A → ℂ) (H₁ : Subgroup K) (hH₁ : ∀ h ∈ H₁, h • χ = χ) (h : H₁) :
    stabRep σ A χ H₁ hH₁ h = (σ h).restrict (mapsTo_of_smul_eq σ A (hH₁ h h.2)) := rfl

end Rep

section Trace

variable {W : Type v} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]

omit [FiniteDimensional ℂ W] in
private theorem mapsTo_of_eq {ι : Type*} {N : ι → Submodule ℂ W} {f : W →ₗ[ℂ] W} {i j : ι}
    (hf : Set.MapsTo f (N i) (N j)) (h : j = i) : Set.MapsTo f (N i) (N i) := h ▸ hf

private theorem trace_eq_sum_fixed {ι : Type*} [DecidableEq ι] {N : ι → Submodule ℂ W}
    (h : DirectSum.IsInternal N)
    (s : Finset ι) (hs : ∀ i, N i ≠ ⊥ → i ∈ s) (π : ι → ι) (f : W →ₗ[ℂ] W)
    (hf : ∀ i, Set.MapsTo f (N i) (N (π i))) :
    LinearMap.trace ℂ W f =
      ∑ i ∈ s, if hi : π i = i then LinearMap.trace ℂ (N i) (f.restrict (mapsTo_of_eq (hf i) hi))
        else 0 := by
  have hN : {i | N i ≠ ⊥}.Finite := WellFoundedGT.finite_ne_bot_of_iSupIndep h.submodule_iSupIndep
  set s₀ := hN.toFinset with hs₀
  have hmem₀ : ∀ i, i ∈ s₀ ↔ N i ≠ ⊥ := fun i => by simp [hs₀]
  have hzero : ∀ i, N i = ⊥ →
      (if hi : π i = i then LinearMap.trace ℂ (N i) (f.restrict (mapsTo_of_eq (hf i) hi))
        else 0) = 0 := by
    intro i hi
    split_ifs with hπ
    · have : Subsingleton (N i) := by
        rw [hi]; infer_instance
      rw [Subsingleton.elim (f.restrict (mapsTo_of_eq (hf i) hπ)) 0, map_zero]
    · rfl
  have hsum : (∑ i ∈ s, if hi : π i = i then
        LinearMap.trace ℂ (N i) (f.restrict (mapsTo_of_eq (hf i) hi)) else 0) =
      ∑ i ∈ s₀, if hi : π i = i then
        LinearMap.trace ℂ (N i) (f.restrict (mapsTo_of_eq (hf i) hi)) else 0 := by
    apply (Finset.sum_subset _ _).symm
    · intro i hi
      exact hs i ((hmem₀ i).1 hi)
    · intro i _ hi
      apply hzero
      by_contra hne
      exact hi ((hmem₀ i).2 hne)
  rw [hsum]
  replace h : DirectSum.IsInternal fun i : s₀ => N i := by
    convert DirectSum.isInternal_ne_bot_iff.mpr h <;> simp [hs₀]
  let κ := fun i : ι => Fin (Module.finrank ℂ (N i))
  let b : (i : s₀) → Basis (κ i) ℂ (N i) := fun i => Module.finBasis ℂ (N i)
  rw [LinearMap.trace_eq_matrix_trace ℂ (h.collectedBasis b), Matrix.trace]
  simp only [Matrix.diag_apply]
  rw [Fintype.sum_sigma, ← Finset.sum_coe_sort s₀]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hπ : π (i : ι) = i
  · rw [dite_eq_left hπ, LinearMap.trace_eq_matrix_trace ℂ (b i), Matrix.trace]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply, LinearMap.toMatrix_apply,
      DirectSum.IsInternal.collectedBasis_coe]
    have hx : f (b i k) ∈ N i := mapsTo_of_eq (hf i) hπ (b i k).2
    rw [h.collectedBasis_repr_of_mem b hx]
    congr 2
  · rw [dite_eq_right hπ]
    apply Finset.sum_eq_zero
    intro k _
    rw [LinearMap.toMatrix_apply, DirectSum.IsInternal.collectedBasis_coe]
    have hx : f (b i k) ∈ N (π i) := hf i (b i k).2
    by_cases hπs : π (i : ι) ∈ s₀
    · have hne : (⟨π i, hπs⟩ : s₀) ≠ i := fun heq => hπ (congrArg Subtype.val heq)
      exact h.collectedBasis_repr_of_mem_ne b hne hx
    · have hbot : N (π i) = ⊥ := by
        by_contra hne; exact hπs ((hmem₀ _).2 hne)
      rw [hbot, Submodule.mem_bot] at hx
      simp [hx]

end Trace

section GroupLemma

variable {K : Type u} [Group K] [Finite K] {Γ : Type w} [Group Γ]

private theorem exists_normal_comm_not_central {p : ℕ} (hp : p.Prime) (A : Subgroup K)
    [hAn : A.Normal]
    (hpow : ∀ k : K, ∃ n : ℕ, k ^ p ^ n ∈ A) (f : K →* Γ)
    (hAcomm : ∀ a ∈ A, ∀ b ∈ A, f a * f b = f b * f a)
    (hnc : ∃ x y : K, f x * f y ≠ f y * f x) :
    ∃ B : Subgroup K, B.Normal ∧ A ≤ B ∧ (∀ a ∈ B, ∀ b ∈ B, f a * f b = f b * f a) ∧
      ∃ b ∈ B, ∃ k : K, f b * f k ≠ f k * f b := by
  by_cases hcase : ∃ a ∈ A, ∃ k : K, f a * f k ≠ f k * f a
  · obtain ⟨a, ha, k, hk⟩ := hcase
    exact ⟨A, hAn, le_rfl, hAcomm, a, ha, k, hk⟩
  · push Not at hcase
    let Z : Subgroup K :=
      { carrier := {z | ∀ k : K, f z * f k = f k * f z}
        one_mem' := by intro k; simp
        mul_mem' := fun {a b} ha hb k => by
          rw [map_mul, mul_assoc, hb k, ← mul_assoc, ha k, mul_assoc]
        inv_mem' := fun {a} ha k => by
          rw [map_inv]
          have := ha k
          calc (f a)⁻¹ * f k = (f a)⁻¹ * (f k * f a) * (f a)⁻¹ := by group
            _ = (f a)⁻¹ * (f a * f k) * (f a)⁻¹ := by rw [this]
            _ = f k * (f a)⁻¹ := by group }
    have hZmem : ∀ z, z ∈ Z ↔ ∀ k : K, f z * f k = f k * f z := fun z => Iff.rfl
    have hZn : Z.Normal := ⟨fun z hz g k => by
      rw [hZmem] at hz
      have h1 := hz (g⁻¹ * k * g)
      simp only [map_mul, map_inv] at h1 ⊢
      calc f g * f z * (f g)⁻¹ * f k = f g * (f z * ((f g)⁻¹ * f k * f g)) * (f g)⁻¹ := by group
        _ = f g * (((f g)⁻¹ * f k * f g) * f z) * (f g)⁻¹ := by rw [h1]
        _ = f k * (f g * f z * (f g)⁻¹) := by group⟩
    have hAZ : A ≤ Z := fun a ha k => hcase a ha k
    have : Fact p.Prime := ⟨hp⟩
    have hPG : IsPGroup p (K ⧸ Z) := by
      intro x
      induction x using QuotientGroup.induction_on with
      | H k =>
        obtain ⟨n, hn⟩ := hpow k
        exact ⟨n, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hAZ hn⟩
    obtain ⟨x, y, hxy⟩ := hnc
    have hnt : Nontrivial (K ⧸ Z) := by
      refine ⟨⟨(x : K ⧸ Z), 1, ?_⟩⟩
      intro hx1
      rw [QuotientGroup.eq_one_iff, hZmem] at hx1
      exact hxy (hx1 y)
    obtain ⟨⟨zbar, hzc⟩, hz1⟩ :=
      (nontrivial_iff_exists_ne (1 : Subgroup.center (K ⧸ Z))).1 hPG.center_nontrivial
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective zbar
    have hzZ : z ∉ Z := by
      intro h
      apply hz1
      apply Subtype.ext
      change (z : K ⧸ Z) = 1
      rwa [QuotientGroup.eq_one_iff]
    have hzcomm : ∀ k : K, k * z * k⁻¹ * z⁻¹ ∈ Z := by
      intro k
      rw [Subgroup.mem_center_iff] at hzc
      have := hzc (k : K ⧸ Z)
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at this
      have h2 : k * ((k * z)⁻¹ * (z * k)) * k⁻¹ ∈ Z := hZn.conj_mem _ this k
      have h3 : (k * ((k * z)⁻¹ * (z * k)) * k⁻¹)⁻¹ ∈ Z := Z.inv_mem h2
      have h4 := hZn.conj_mem _ h3 z
      have e : z * (k * ((k * z)⁻¹ * (z * k)) * k⁻¹)⁻¹ * z⁻¹ = k * z * k⁻¹ * z⁻¹ := by group
      rwa [e] at h4
    let B : Subgroup K := Subgroup.zpowers z ⊔ Z
    have hBmem : ∀ b : K, b ∈ B ↔ ∃ i : ℤ, ∃ w ∈ Z, z ^ i * w = b := by
      intro b
      have : b ∈ B ↔ b ∈ ((Subgroup.zpowers z ⊔ Z : Subgroup K) : Set K) := Iff.rfl
      rw [this, Subgroup.mul_normal, Set.mem_mul]
      constructor
      · rintro ⟨u, hu, w, hw, rfl⟩
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
        exact ⟨i, w, hw, rfl⟩
      · rintro ⟨i, w, hw, rfl⟩
        exact ⟨z ^ i, Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) i, w, hw, rfl⟩
    have hzB : z ∈ B := Subgroup.mem_sup_left (Subgroup.mem_zpowers z)
    have hZB : Z ≤ B := le_sup_right
    refine ⟨B, ?_, hAZ.trans hZB, ?_, z, hzB, ?_⟩
    · refine ⟨fun b hb g => ?_⟩
      obtain ⟨i, w, hw, rfl⟩ := (hBmem b).1 hb
      have e : g * (z ^ i * w) * g⁻¹ = (g * z * g⁻¹) ^ i * (g * w * g⁻¹) := by
        rw [conj_zpow]; group
      rw [e]
      refine B.mul_mem (B.zpow_mem ?_ i) (hZB (hZn.conj_mem w hw g))
      have e2 : g * z * g⁻¹ = (g * z * g⁻¹ * z⁻¹) * z := by group
      rw [e2]
      exact B.mul_mem (hZB (hzcomm g)) hzB
    · intro a ha b hb
      obtain ⟨i, w, hw, rfl⟩ := (hBmem a).1 ha
      obtain ⟨j, w', hw', rfl⟩ := (hBmem b).1 hb
      have hw1 := (hZmem w).1 hw
      have hw2 := (hZmem w').1 hw'
      simp only [map_mul, map_zpow]
      have c1 : f w * f (z ^ j) = f (z ^ j) * f w := hw1 (z ^ j)
      have c2 : f w * f w' = f w' * f w := hw1 w'
      have c3 : f w' * f (z ^ i) = f (z ^ i) * f w' := hw2 (z ^ i)
      rw [map_zpow] at c1 c3
      calc f z ^ i * f w * (f z ^ j * f w') = f z ^ i * (f w * f z ^ j) * f w' := by group
        _ = f z ^ i * (f z ^ j * f w) * f w' := by rw [c1]
        _ = f z ^ j * f z ^ i * (f w * f w') := by
            have hz2 : f z ^ i * f z ^ j = f z ^ j * f z ^ i := by
              rw [← zpow_add, ← zpow_add, add_comm]
            rw [show f z ^ i * (f z ^ j * f w) * f w' = (f z ^ i * f z ^ j) * (f w * f w') by group,
              hz2]
        _ = f z ^ j * f z ^ i * (f w' * f w) := by rw [c2]
        _ = f z ^ j * (f z ^ i * f w') * f w := by group
        _ = f z ^ j * (f w' * f z ^ i) * f w := by rw [c3]
        _ = f z ^ j * f w' * (f z ^ i * f w) := by group
    · by_contra hall
      push Not at hall
      exact hzZ ((hZmem z).2 hall)

end GroupLemma

section Induction

private def Monomial (K : Type u) [Group K] [Fintype K] (W : Type v) [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (σ : Representation ℂ K W) : Prop :=
  ∃ l : List (Entry K), ∀ g : K, LinearMap.trace ℂ W (σ g) = lsum l g

variable {K : Type u} [Group K] [Fintype K]
variable {W : Type v} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
variable (σ : Representation ℂ K W)

private theorem monomial_of_finrank_zero (h : Module.finrank ℂ W = 0) : Monomial K W σ := by
  have : Subsingleton W := Module.finrank_zero_iff.1 h
  refine ⟨[], fun g => ?_⟩
  have : σ g = 0 := LinearMap.ext fun v => Subsingleton.elim _ _
  rw [this, map_zero, lsum_nil, Pi.zero_apply]

open scoped Classical in
private theorem monomial_of_comm (hab : ∀ x y : K, σ x * σ y = σ y * σ x) : Monomial K W σ := by
  let T : Subgroup K := ⊤
  have hcommT : ∀ a b : T, σ a * σ b = σ b * σ a := fun a b => hab a b
  have hint := isInternal_wt σ T hcommT
  have hfin := finite_wt σ T hint
  set S := hfin.toFinset with hS
  have hSmem : ∀ χ, χ ∈ S ↔ wt σ T χ ≠ ⊥ := fun χ => by simp [hS]
  let ent : (T → ℂ) → Entry K := fun χ =>
    if hχ : wt σ T χ ≠ ⊥ then ⟨⊤, weightHom σ T hχ⟩ else ⟨⊤, 1⟩
  have hval : ∀ χ, ∀ hχ : wt σ T χ ≠ ⊥, ∀ g : K, val (ent χ) g = χ ⟨g, Subgroup.mem_top g⟩ := by
    intro χ hχ g
    have hent : ent χ = ⟨⊤, weightHom σ T hχ⟩ := by simp only [ent, dite_eq_left hχ]
    rw [hent, val]
    have hcf : ∀ x y : K, extChar ⊤ (weightHom σ T hχ) (x⁻¹ * y * x) =
        extChar ⊤ (weightHom σ T hχ) y := by
      intro x y
      simp only [extChar, dite_eq_left (Subgroup.mem_top _), weightHom_apply]
      have e : (⟨x⁻¹ * y * x, Subgroup.mem_top _⟩ : T) =
          (⟨x, Subgroup.mem_top _⟩ : T)⁻¹ * ⟨y, Subgroup.mem_top _⟩ * ⟨x, Subgroup.mem_top _⟩ := rfl
      rw [e, weight_mul σ T hχ, weight_mul σ T hχ, mul_comm (χ _) (χ ⟨y, _⟩), mul_assoc,
        ← weight_mul σ T hχ, inv_mul_cancel, weight_one σ T hχ, mul_one]
    change ClassFunction.induced ⊤ (extChar ⊤ (weightHom σ T hχ)) g = _
    rw [ClassFunction.induced_top_of_conj_invariant _ hcf]
    simp only [extChar, dite_eq_left (Subgroup.mem_top _), weightHom_apply]
  have htr : ∀ g : K, LinearMap.trace ℂ W (σ g) =
      ∑ χ ∈ S, χ ⟨g, Subgroup.mem_top g⟩ * (Module.finrank ℂ (wt σ T χ) : ℂ) := by
    intro g
    have hf : ∀ χ : T → ℂ, Set.MapsTo (σ g) (wt σ T χ) (wt σ T χ) :=
      fun χ => mapsTo_wt_of_comm σ T χ (σ g) (fun a => hab g a)
    rw [LinearMap.trace_eq_sum_trace_restrict' hint hfin hf]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    have hres : (σ g).restrict (hf χ) = χ ⟨g, Subgroup.mem_top g⟩ • LinearMap.id := by
      apply LinearMap.ext; intro v; apply Subtype.ext
      simp only [LinearMap.smul_apply, LinearMap.id_apply,
        Submodule.coe_smul]
      exact (mem_wt σ T χ v).1 v.2 ⟨g, Subgroup.mem_top g⟩
    rw [hres, map_smul, LinearMap.trace_id, smul_eq_mul]
  refine ⟨(S.toList.map fun χ => List.replicate (Module.finrank ℂ (wt σ T χ)) (ent χ)).flatten,
    fun g => ?_⟩
  rw [htr g, lsum_flatten_replicate, Finset.sum_map_toList]
  refine Finset.sum_congr rfl fun χ hχ => ?_
  rw [hval χ ((hSmem χ).1 hχ) g, mul_comm]

private theorem monomial_of_isCompl (P₁ P₂ : Submodule ℂ W) (hc : IsCompl P₁ P₂)
    (h₁ : ∀ k : K, P₁ ≤ P₁.comap (σ k)) (h₂ : ∀ k : K, P₂ ≤ P₂.comap (σ k))
    (m₁ : Monomial K P₁ (σ.subrepresentation P₁ h₁))
    (m₂ : Monomial K P₂ (σ.subrepresentation P₂ h₂)) : Monomial K W σ := by
  obtain ⟨l₁, hl₁⟩ := m₁
  obtain ⟨l₂, hl₂⟩ := m₂
  refine ⟨l₁ ++ l₂, fun g => ?_⟩
  rw [lsum_append, Pi.add_apply, ← hl₁, ← hl₂]
  set e := Submodule.prodEquivOfIsCompl P₁ P₂ hc with he
  have : σ g =
      e.conj (((σ.subrepresentation P₁ h₁) g).prodMap ((σ.subrepresentation P₂ h₂) g)) := by
    apply LinearMap.ext
    intro v
    rw [LinearEquiv.conj_apply_apply]
    obtain ⟨⟨a, b⟩, rfl⟩ := e.surjective v
    rw [LinearEquiv.symm_apply_apply, LinearMap.prodMap_apply, he,
      Submodule.coe_prodEquivOfIsCompl', Submodule.coe_prodEquivOfIsCompl', map_add]
    rfl
  rw [this, LinearMap.trace_conj', LinearMap.trace_prodMap']

open scoped Classical in
private theorem monomial_of_transitive (B : Subgroup K) [B.Normal]
    (hcommB : ∀ a b : B, σ a * σ b = σ b * σ a)
    (S : Finset (B → ℂ)) (hS : ∀ χ, χ ∈ S ↔ wt σ B χ ≠ ⊥) (χ₁ : B → ℂ) (hχ₁ : χ₁ ∈ S)
    (htrans : ∀ χ ∈ S, χ ∈ MulAction.orbit K χ₁)
    (H₁ : Subgroup K) (hH₁ : ∀ h : K, h ∈ H₁ ↔ h • χ₁ = χ₁)
    (m : Monomial H₁ (wt σ B χ₁) (stabRep σ B χ₁ H₁ (fun h hh => (hH₁ h).1 hh))) :
    Monomial K W σ := by
  obtain ⟨l', hl'⟩ := m
  refine ⟨l'.map (lift H₁), fun g => ?_⟩
  rw [← induced_lsum_eq]
  suffices key : ∀ Φ : K → ℂ,
      (∀ (y : K) (hy : y ∈ H₁), Φ y =
        LinearMap.trace ℂ _ (stabRep σ B χ₁ H₁ (fun h hh => (hH₁ h).1 hh) ⟨y, hy⟩)) →
      LinearMap.trace ℂ W (σ g) = ClassFunction.induced H₁ Φ g by
    apply key
    intro y hy
    rw [dite_eq_left hy]
    exact (hl' ⟨y, hy⟩).symm
  intro Φ hΦ
  rw [ClassFunction.induced_apply]
  have hint := isInternal_wt σ B hcommB
  have horbS : ∀ x : K, x • χ₁ ∈ S := fun x =>
    (hS _).2 ((wt_smul_ne_bot_iff σ B x χ₁).2 ((hS _).1 hχ₁))
  let D : (B → ℂ) → ℂ := fun χ => if hχ : g • χ = χ then
    LinearMap.trace ℂ (wt σ B χ) ((σ g).restrict (mapsTo_of_eq (mapsTo_smul σ B g χ) hχ)) else 0
  have hD : LinearMap.trace ℂ W (σ g) = ∑ χ ∈ S, D χ :=
    trace_eq_sum_fixed hint S (fun χ h => (hS χ).2 h) (fun χ => g • χ) (σ g) (mapsTo_smul σ B g)
  have hstep1 : ∀ x : K, (if x⁻¹ * g * x ∈ H₁ then Φ (x⁻¹ * g * x) else 0) = D (x • χ₁) := by
    intro x
    have hiff : x⁻¹ * g * x ∈ H₁ ↔ g • (x • χ₁) = x • χ₁ := by
      rw [hH₁, mul_smul, mul_smul, inv_smul_eq_iff]
    by_cases hx : x⁻¹ * g * x ∈ H₁
    · rw [ite_eq_left hx, hΦ _ hx]
      simp only [D, dite_eq_left (hiff.1 hx)]
      rw [stabRep_apply]
      exact (trace_restrict_conj σ B x g χ₁ _ _).symm
    · rw [ite_eq_right hx]
      simp only [D, dite_eq_right (mt hiff.2 hx)]
  have hstep2 : ∑ x : K, D (x • χ₁) = (Nat.card H₁ : ℂ) * ∑ χ ∈ S, D χ := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := S) (g := fun x : K => x • χ₁)
      (fun x _ => horbS x) (fun x => D (x • χ₁)), Finset.mul_sum]
    refine Finset.sum_congr rfl fun χ hχ => ?_
    have : ∑ x ∈ Finset.univ.filter (fun x : K => x • χ₁ = χ), D (x • χ₁) =
        ∑ x ∈ Finset.univ.filter (fun x : K => x • χ₁ = χ), D χ := by
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [(Finset.mem_filter.1 hx).2]
    rw [this, Finset.sum_const, nsmul_eq_mul]
    congr 1
    obtain ⟨k, rfl⟩ := MulAction.mem_orbit_iff.1 (htrans χ hχ)
    have hcard : Nat.card {x : K // x • χ₁ = k • χ₁} =
        (Finset.univ.filter fun x : K => x • χ₁ = k • χ₁).card := Nat.subtype_card _ (by simp)
    have hcard2 : Nat.card {x : K // x • χ₁ = k • χ₁} = Nat.card H₁ := by
      apply Nat.card_congr
      exact
        { toFun := fun x => ⟨k⁻¹ * x.1, by
            rw [hH₁, mul_smul, x.2, inv_smul_smul]⟩
          invFun := fun h => ⟨k * h.1, by
            rw [mul_smul, (hH₁ _).1 h.2]⟩
          left_inv := fun x => by simp
          right_inv := fun h => by simp }
    rw [← hcard2, hcard]
  rw [Finset.sum_congr rfl (fun x _ => hstep1 x), hstep2, hD, ← mul_assoc]
  have hne : (Nat.card H₁ : ℂ) ≠ 0 := by exact_mod_cast Nat.card_pos.ne'
  rw [inv_mul_cancel₀ hne, one_mul]

open scoped Classical in
private theorem engine {p : ℕ} (hp : p.Prime) : ∀ (m : ℕ) (K : Type u) [Group K] [Fintype K]
    (W : Type v) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (σ : Representation ℂ K W),
    Fintype.card K + Module.finrank ℂ W ≤ m →
    ∀ (A : Subgroup K) [A.Normal], (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) →
      (∀ k : K, ∃ n : ℕ, k ^ p ^ n ∈ A) → Monomial K W σ := by
  intro m
  induction m with
  | zero =>
    intro K _ _ W _ _ _ σ hm
    exfalso
    have := Fintype.card_pos (α := K)
    omega
  | succ m ih =>
    intro K _ _ W _ _ _ σ hm A hAn hAcomm hpow
    by_cases hW : Module.finrank ℂ W = 0
    · exact monomial_of_finrank_zero σ hW
    by_cases hab : ∀ x y : K, σ x * σ y = σ y * σ x
    · exact monomial_of_comm σ hab
    push Not at hab
    obtain ⟨x, y, hxy⟩ := hab
    let f := σ.toHomUnits
    have hf : ∀ k, ((f k : (W →ₗ[ℂ] W)ˣ) : W →ₗ[ℂ] W) = σ k := fun k => rfl
    obtain ⟨B, hBn, hAB, hBcomm, b₀, hb₀, k₀, hbk⟩ := exists_normal_comm_not_central hp A hpow f
      (fun a ha b hb => Units.ext (by
        simp only [hf, ← map_mul, hAcomm a ha b hb]))
      ⟨x, y, fun h => hxy (by simpa [hf] using congrArg Units.val h)⟩
    have := hBn
    have hcommB : ∀ a b : B, σ a * σ b = σ b * σ a := fun a b => by
      simpa [hf] using congrArg Units.val (hBcomm a a.2 b b.2)
    have hbk' : σ b₀ * σ k₀ ≠ σ k₀ * σ b₀ := fun h => hbk (Units.ext (by simpa [hf] using h))
    have hint := isInternal_wt σ B hcommB
    have hfin := finite_wt σ B hint
    set S := hfin.toFinset with hS
    have hSmem : ∀ χ, χ ∈ S ↔ wt σ B χ ≠ ⊥ := fun χ => by simp [hS]
    have hW' : Nontrivial W := Module.finrank_pos_iff.1 (Nat.pos_of_ne_zero hW)
    obtain ⟨χ₁, hχ₁⟩ : ∃ χ₁, χ₁ ∈ S := by
      by_contra hnone
      push Not at hnone
      have htop := hint.submodule_iSup_eq_top
      have : (⨆ χ, wt σ B χ) = ⊥ := by
        apply iSup_eq_bot.2
        intro χ
        by_contra hne
        exact hnone χ ((hSmem χ).2 hne)
      rw [this] at htop
      exact bot_ne_top htop
    obtain ⟨χ₂, hχ₂, hne⟩ : ∃ χ₂ ∈ S, χ₂ ≠ χ₁ := by
      by_contra hall
      push Not at hall
      have htop : wt σ B χ₁ = ⊤ := by
        rw [eq_top_iff, ← hint.submodule_iSup_eq_top]
        apply iSup_le
        intro χ
        by_cases hχ : wt σ B χ = ⊥
        · rw [hχ]; exact bot_le
        · rw [hall χ ((hSmem χ).2 hχ)]
      apply hbk'
      apply LinearMap.ext
      intro v
      have hv : ∀ w : W, σ b₀ w = χ₁ ⟨b₀, hb₀⟩ • w := fun w =>
        (mem_wt σ B χ₁ w).1 (htop ▸ Submodule.mem_top) ⟨b₀, hb₀⟩
      simp only [mul_apply_eq_comp, hv, map_smul]
    by_cases htr : ∀ χ ∈ S, χ ∈ MulAction.orbit K χ₁
    · obtain ⟨H₁, hH₁⟩ : ∃ H₁ : Subgroup K, ∀ h : K, h ∈ H₁ ↔ h • χ₁ = χ₁ :=
        ⟨MulAction.stabilizer K χ₁, fun h => MulAction.mem_stabilizer_iff⟩
      have hH₁top : H₁ ≠ ⊤ := by
        intro htopH
        obtain ⟨k, rfl⟩ := MulAction.mem_orbit_iff.1 (htr χ₂ hχ₂)
        apply hne
        have : k ∈ H₁ := htopH ▸ Subgroup.mem_top k
        exact (hH₁ k).1 this
      have hcard : Fintype.card H₁ < Fintype.card K := by
        have h1 := Subgroup.card_mul_index H₁
        have h2 := Subgroup.one_lt_index_of_ne_top hH₁top
        rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h1
        have h3 := Fintype.card_pos (α := H₁)
        nlinarith
      have hdim : Module.finrank ℂ (wt σ B χ₁) ≤ Module.finrank ℂ W := Submodule.finrank_le _
      apply monomial_of_transitive σ B hcommB S hSmem χ₁ hχ₁ htr H₁ hH₁
      apply ih (↥H₁) (wt σ B χ₁) (stabRep σ B χ₁ H₁ fun h hh => (hH₁ h).1 hh) (by omega)
        (A.subgroupOf H₁)
      · intro a ha b hb
        apply Subtype.ext
        exact hAcomm a ha b hb
      · intro h
        obtain ⟨n, hn⟩ := hpow h
        exact ⟨n, by rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]; exact hn⟩
    · push Not at htr
      obtain ⟨χ₃, hχ₃, hno⟩ := htr
      let O := MulAction.orbit K χ₁
      let P₁ : Submodule ℂ W := ⨆ χ ∈ O, wt σ B χ
      let P₂ : Submodule ℂ W := ⨆ χ ∈ Oᶜ, wt σ B χ
      have hc : IsCompl P₁ P₂ := by
        constructor
        · exact hint.submodule_iSupIndep.disjoint_biSup_biSup disjoint_compl_right
        · rw [codisjoint_iff]
          have : P₁ ⊔ P₂ = ⨆ χ, wt σ B χ := by
            change (⨆ χ ∈ O, wt σ B χ) ⊔ (⨆ χ ∈ Oᶜ, wt σ B χ) = _
            rw [← iSup_union, Set.union_compl_self, iSup_univ]
          rw [this, hint.submodule_iSup_eq_top]
      have hstab : ∀ (T : Set (B → ℂ)), (∀ k : K, ∀ χ ∈ T, k • χ ∈ T) →
          ∀ k : K, (⨆ χ ∈ T, wt σ B χ) ≤ (⨆ χ ∈ T, wt σ B χ).comap (σ k) := by
        intro T hT k
        rw [← Submodule.map_le_iff_le_comap, Submodule.map_iSup]
        apply iSup_le
        intro χ
        rw [Submodule.map_iSup]
        apply iSup_le
        intro hχ
        refine le_trans ?_ (le_biSup (fun χ => wt σ B χ) (hT k χ hχ))
        rintro _ ⟨v, hv, rfl⟩
        exact mapsTo_smul σ B k χ hv
      have hO : ∀ k : K, ∀ χ ∈ O, k • χ ∈ O := by
        intro k χ hχ
        obtain ⟨j, rfl⟩ := MulAction.mem_orbit_iff.1 hχ
        exact MulAction.mem_orbit_iff.2 ⟨k * j, mul_smul k j χ₁⟩
      have hOc : ∀ k : K, ∀ χ ∈ Oᶜ, k • χ ∈ Oᶜ := by
        intro k χ hχ hk
        apply hχ
        have := hO k⁻¹ _ hk
        rwa [inv_smul_smul] at this
      have h₁ := hstab O hO
      have h₂ := hstab Oᶜ hOc
      have hP₁ : P₁ ≠ ⊥ := by
        intro hbot
        apply (hSmem χ₁).1 hχ₁
        rw [eq_bot_iff, ← hbot]
        exact le_biSup (fun χ => wt σ B χ) (MulAction.mem_orbit_self χ₁)
      have hP₂ : P₂ ≠ ⊥ := by
        intro hbot
        apply (hSmem χ₃).1 hχ₃
        rw [eq_bot_iff, ← hbot]
        exact le_biSup (fun χ => wt σ B χ) hno
      have hsum := Submodule.finrank_add_eq_of_isCompl hc
      have hp1 : 0 < Module.finrank ℂ P₁ :=
        Nat.pos_of_ne_zero (fun h => hP₁ (Submodule.finrank_eq_zero.1 h))
      have hp2 : 0 < Module.finrank ℂ P₂ :=
        Nat.pos_of_ne_zero (fun h => hP₂ (Submodule.finrank_eq_zero.1 h))
      apply monomial_of_isCompl σ P₁ P₂ hc h₁ h₂
      · exact ih K P₁ (σ.subrepresentation P₁ h₁) (by omega) A hAcomm hpow
      · exact ih K P₂ (σ.subrepresentation P₂ h₂) (by omega) A hAcomm hpow

end Induction

section Final

variable {G : Type u} [Group G] [Fintype G] {n : ℕ}

private def repOfGL (ρ : G →* GL (Fin n) ℂ) : Representation ℂ G (Fin n → ℂ) where
  toFun g := Matrix.toLin' ((ρ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
  map_one' := by
    rw [map_one, Units.val_one, Matrix.toLin'_one]
    rfl
  map_mul' x y := by
    rw [map_mul, Units.val_mul, Matrix.toLin'_mul]
    rfl

omit [Fintype G] in
private theorem repOfGL_apply (ρ : G →* GL (Fin n) ℂ) (g : G) :
    repOfGL ρ g = Matrix.toLin' ((ρ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) := rfl

omit [Fintype G] in
private theorem trace_repOfGL (ρ : G →* GL (Fin n) ℂ) (g : G) :
    LinearMap.trace ℂ _ (repOfGL ρ g) =
      ((ρ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace := by
  rw [repOfGL_apply, LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin n)),
    LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin']

open scoped Classical in
private theorem main {p : ℕ} (hp : p.Prime) (A : Subgroup G) (hA : A.Normal)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hquot : ∀ g : G, ∃ n : ℕ, g ^ p ^ n ∈ A)
    (ρ : G →* GL (Fin n) ℂ) :
    ∃ (k : ℕ) (H : Fin k → Subgroup G) (ψ : (i : Fin k) → (H i →* ℂˣ)),
      ∀ g : G, ((ρ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace =
        ∑ i : Fin k, ClassFunction.induced (H i)
          (fun x => if hx : x ∈ H i then (((ψ i) ⟨x, hx⟩ : ℂˣ) : ℂ) else 0) g := by
  have := hA
  obtain ⟨l, hl⟩ := engine hp _ G (Fin n → ℂ) (repOfGL ρ) le_rfl A hcomm hquot
  refine ⟨l.length, fun i => (l.get i).1, fun i => (l.get i).2, fun g => ?_⟩
  rw [← trace_repOfGL, hl g, lsum]
  conv_lhs => rw [← List.ofFn_get l, List.map_ofFn, List.sum_ofFn]
  rfl

end Final

end MonomialProof

open scoped MatrixGroups Classical in
/-- **Monomial characters.** Let `G` be a finite group with an abelian normal subgroup `A`
such that every element of `G` has a `p`-power in `A`, for a prime `p`. Then the character
`g ↦ trace (ρ g)` of every complex representation `ρ : G →* GL (Fin n) ℂ` is a sum, with every
coefficient `1`, of characters `induced (H i) (ψ i)` induced over `ℂ` from linear characters
`ψ i : H i →* ℂˣ` of subgroups `H i`, each `ψ i` extended by zero off `H i`. -/
public theorem exists_trace_eq_sum_induced_linearCharacter_of_normal_comm_of_pow_prime_pow_mem
    {G : Type u} [Group G] [Fintype G] {p : ℕ} (hp : p.Prime) (A : Subgroup G) (hA : A.Normal)
    (hcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hquot : ∀ g : G, ∃ n : ℕ, g ^ p ^ n ∈ A)
    {n : ℕ} (ρ : G →* GL (Fin n) ℂ) :
    ∃ (k : ℕ) (H : Fin k → Subgroup G) (ψ : (i : Fin k) → (H i →* ℂˣ)),
      ∀ g : G, ((ρ g : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).trace =
        ∑ i : Fin k, ClassFunction.induced (H i)
          (fun x => if hx : x ∈ H i then (((ψ i) ⟨x, hx⟩ : ℂˣ) : ℂ) else 0) g :=
  MonomialProof.main hp A hA hcomm hquot ρ

end ClassFunction

end
