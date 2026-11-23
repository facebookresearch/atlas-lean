/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-
Modifications copyright (c) 2026 Meta Platforms, Inc. and affiliates.
-/
/-
Ported from TauCetiProject/TauCeti at
62bbc0596dc3539d488232e4e924a338548ea0a9:
TauCeti/LinearAlgebra/End/LocallyNilpotent.lean
Public source: https://github.com/TauCetiProject/TauCeti
The original contributors' copyright, author and Apache License 2.0
notice is retained above. Modification notice: use the explicitly
listed MathlibExt ports for this complete SBI dependency closure;
retain the mathematical declarations and original names. Identity-scalar
multilinear maps and endomorphism-application lemmas use the pinned
Mathlib API; the finite-coordinate port keeps only its four needed lemmas.
-/
module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Submodule.Basic
public import Mathlib.Algebra.Module.Submodule.Range
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import MathlibExt.LinearAlgebra.CyclicGradedLinearMap

/-!
# Locally nilpotent endomorphisms and families of endomorphisms

An endomorphism `f` of a module is *locally nilpotent* when every vector is annihilated by some
power of `f`.  Then `1 + f` is invertible.  No global nilpotence bound is needed, so the statement
applies to operators which lower a filtration by direct summands without being nilpotent on the
whole module, such as those of homological perturbation theory on bar constructions.

On a free module `ι →₀ R`, an endomorphism is locally nilpotent as soon as it strictly lowers a
weight on the basis whose strict order is well-founded, for instance any weight on a finite basis.

More generally, a family `f i` of endomorphisms is locally nilpotent when every vector is killed by
all sufficiently long composites `f i₁ ∘ ⋯ ∘ f i_d`. The vectors killed by all composites of
length `d` form a submodule `Module.End.wordKer f d`, and local nilpotence is the statement
`⨆ d, Module.End.wordKer f d = ⊤`. It passes to submodules and quotients stable under the family.
If no nonzero vector is killed by every `f i`, then `Module.End.wordKer f d = ⊥` for every `d`, so
a locally nilpotent family with this property can only act on the zero module. Operators lowering
a grading by `ℕ`, such as divided differences on a polynomial ring, form locally nilpotent families.

## Main results

* `IsNilpotent.exists_pow_apply_eq_zero`: a nilpotent endomorphism is locally nilpotent.
* `Module.End.sum_range_smul_pow_apply_eq_of_le`: at a vector killed by `f ^ k`, a power series in
  `f` may be truncated at any length beyond `k`.
* `Module.End.span_range_pow_apply_eq_span_range_fin`: the orbit of a vector killed by
  `u ^ (n + 1)` spans the same submodule as its first `n + 1` vectors.
* `Module.End.neg_pow_apply_eq_zero_iff`: a power of `-f` kills a vector exactly when the same
  power of `f` does.
* `Module.End.isUnit_one_add_of_forall_exists_pow_apply_eq_zero`: `1 + f` is a unit when `f` is
  locally nilpotent.
* `Module.End.bijective_of_sub_mem_filtration`: an endomorphism which is the identity up to a
  map lowering an exhaustive filtration starting at `⊥` is bijective.
* `TauCeti.LinearMap.IsHomogeneous.ringInverse_one_add`: the inverse of `1 + f` has degree zero
  when `f` is locally nilpotent of degree zero.
* `Module.End.exists_pow_apply_eq_zero_of_forall_mem_support_lt`: an endomorphism of `ι →₀ R`
  that strictly lowers a well-founded weight on the basis is locally nilpotent.
* `Module.End.mem_wordKer_iff`: `Module.End.wordKer f d` consists of the vectors killed by the
  composite of every word of length `d` in the family `f`.
* `Module.End.wordKer_eq_bot_of_iInf_ker_eq_bot`: if the family `f` has no common nonzero kernel
  vector, then neither do its composites of any length.
* `Module.End.iSup_wordKer_eq_top_of_surjective`, `Module.End.iSup_wordKer_eq_top_of_injective`:
  local nilpotence of a family passes to quotients and to submodules.
-/

public section

/-- A nilpotent endomorphism is locally nilpotent: each vector is killed by some power of it. -/
theorem IsNilpotent.exists_pow_apply_eq_zero {R M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] {f : Module.End R M} (hf : IsNilpotent f) (x : M) : ∃ n, (f ^ n) x = 0 := by
  obtain ⟨n, hn⟩ := hf
  exact ⟨n, by rw [hn, LinearMap.zero_apply]⟩

/-- A power series in `f` applied to a vector killed by `f ^ k` does not change when it is
truncated at any length beyond `k`, whatever its coefficients. -/
theorem Module.End.sum_range_smul_pow_apply_eq_of_le {R S M : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] [SMulZeroClass S M] (f : Module.End R M) (c : ℕ → S)
    {x : M} {k l : ℕ} (hk : (f ^ k) x = 0) (hkl : k ≤ l) :
    ∑ i ∈ Finset.range l, c i • (f ^ i) x = ∑ i ∈ Finset.range k, c i • (f ^ i) x := by
  have h : ∑ i ∈ Finset.Ico k l, c i • (f ^ i) x = 0 := Finset.sum_eq_zero fun i hi ↦ by
    rw [Module.End.pow_map_zero_of_le (Finset.mem_Ico.1 hi).1 hk, smul_zero]
  rw [← Finset.sum_range_add_sum_Ico _ hkl, h, add_zero]

/-- The orbit `x, u x, u² x, …` of a vector killed by `u ^ (n + 1)` may be truncated to its first
`n + 1` positions without changing its span. -/
theorem Module.End.span_range_pow_apply_eq_span_range_fin {R M : Type*} [Semiring R]
    [AddCommMonoid M] [Module R M] (u : Module.End R M) {x : M} {n : ℕ}
    (h0 : (u ^ (n + 1)) x = 0) :
    Submodule.span R (Set.range fun i : ℕ ↦ (u ^ i) x) =
      Submodule.span R (Set.range fun i : Fin (n + 1) ↦ (u ^ (i : ℕ)) x) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨i, rfl⟩
    rcases le_or_gt i n with hi | hi
    · exact Submodule.subset_span ⟨⟨i, by omega⟩, rfl⟩
    · simp [Module.End.pow_map_zero_of_le hi h0]
  · rintro _ ⟨i, rfl⟩
    exact Submodule.subset_span ⟨(i : ℕ), rfl⟩

variable {R M : Type*} [Semiring R] [AddCommGroup M] [Module R M]

/-- A power of `-f` kills a vector exactly when the same power of `f` does, so `-f` is locally
nilpotent exactly when `f` is. -/
@[simp]
theorem Module.End.neg_pow_apply_eq_zero_iff (f : Module.End R M) (n : ℕ) (x : M) :
    ((-f) ^ n) x = 0 ↔ (f ^ n) x = 0 := by
  rcases neg_one_pow_eq_or (Module.End R M) n with h | h <;>
    simp [neg_pow, h]

/-- If every vector is annihilated by some power of `f`, then `1 + f` is invertible. -/
theorem Module.End.isUnit_one_add_of_forall_exists_pow_apply_eq_zero (f : Module.End R M)
    (hf : ∀ x, ∃ n, (f ^ n) x = 0) : IsUnit (1 + f) := by
  have hneg : ∀ (n : ℕ) (x : M), (f ^ n) x = 0 → ((-f) ^ n) x = 0 :=
    fun n x ↦ (f.neg_pow_apply_eq_zero_iff n x).2
  rw [Module.End.isUnit_iff]
  refine ⟨(injective_iff_map_eq_zero (1 + f)).2 fun x hx ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨n, hn⟩ := hf x
    have h := LinearMap.congr_fun (geom_sum_mul_neg (-f) n) x
    rw [sub_neg_eq_add, Module.End.mul_apply, hx, map_zero, LinearMap.sub_apply,
      Module.End.one_apply, hneg n x hn, sub_zero] at h
    exact h.symm
  · obtain ⟨n, hn⟩ := hf y
    refine ⟨(∑ i ∈ Finset.range n, (-f) ^ i) y, ?_⟩
    have h := LinearMap.congr_fun (mul_neg_geom_sum (-f) n) y
    rwa [sub_neg_eq_add, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      hneg n y hn, sub_zero] at h

/-- If `f` is the identity up to a map lowering an exhaustive increasing filtration `p` with
`p 0 = ⊥`, that is `f x - x ∈ p n` whenever `x ∈ p (n + 1)`, then `f` is bijective: `f - 1` is
locally nilpotent. -/
theorem Module.End.bijective_of_sub_mem_filtration {p : ℕ → Submodule R M} (hp0 : p 0 = ⊥)
    (hp : ∀ x, ∃ n, x ∈ p n) {f : Module.End R M}
    (hf : ∀ n x, x ∈ p (n + 1) → f x - x ∈ p n) : Function.Bijective f := by
  have hnil (n : ℕ) : ∀ x ∈ p n, ((f - 1) ^ n) x = 0 := by
    induction n with
    | zero =>
      intro x hx
      rw [hp0, Submodule.mem_bot] at hx
      rw [hx, map_zero]
    | succ n ih =>
      intro x hx
      rw [pow_succ, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply]
      exact ih _ (hf n x hx)
  have h := (f - 1).isUnit_one_add_of_forall_exists_pow_apply_eq_zero fun x ↦
    (hp x).imp fun n ↦ hnil n x
  rwa [add_sub_cancel, Module.End.isUnit_iff] at h

section Ring

variable {S N : Type*} [Ring S] [AddCommGroup N] [Module S N]

/-- If `f` is locally nilpotent and homogeneous of degree zero for a grading by submodules, then so
is the inverse of `1 + f`: on a homogeneous vector it is a finite geometric series in `-f`. -/
theorem TauCeti.LinearMap.IsHomogeneous.ringInverse_one_add {ι : Type*} [AddMonoid ι]
    {𝒜 : ι → Submodule S N} {f : Module.End S N}
    (hf : TauCeti.LinearMap.IsHomogeneous f 𝒜 𝒜 0) (hnil : ∀ x, ∃ n, (f ^ n) x = 0) :
    TauCeti.LinearMap.IsHomogeneous (Ring.inverse (1 + f)) 𝒜 𝒜 0 := by
  rw [TauCeti.LinearMap.isHomogeneous_def]
  intro p x hx
  obtain ⟨n, hn⟩ := hnil x
  have hpow : ∀ i : ℕ, ((-f) ^ i) x ∈ 𝒜 p := by
    intro i
    induction i with
    | zero => simpa using hx
    | succ i ih =>
      rw [pow_succ', Module.End.mul_apply, LinearMap.neg_apply]
      simpa only [add_zero] using neg_mem (hf.map_mem ih)
  set y := (∑ i ∈ Finset.range n, (-f) ^ i) x with hy_def
  have hy : (1 + f) y = x := by
    have h := LinearMap.congr_fun (mul_neg_geom_sum (-f) n) x
    rwa [sub_neg_eq_add, Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply,
      neg_pow, Module.End.mul_apply, hn, map_zero, sub_zero] at h
  have hinv : Ring.inverse (1 + f) x = y := by
    rw [← hy, ← Module.End.mul_apply,
      Ring.inverse_mul_cancel _ (Module.End.isUnit_one_add_of_forall_exists_pow_apply_eq_zero f
        hnil), Module.End.one_apply]
  rw [hinv, add_zero, hy_def, LinearMap.sum_apply]
  exact Submodule.sum_mem _ fun i _ ↦ hpow i

end Ring

section Finsupp

open Finsupp

variable {R ι α : Type*} [Semiring R] [LT α]

/-- **Strictly lowering a well-founded weight on a basis is locally nilpotent.** Let `w` be a
weight on `ι` whose strict order `w j < w i` is well-founded, as is automatic when `ι` is finite
and `α` is a preorder, or when `<` is well-founded on `α`. If an endomorphism `f` of `ι →₀ R`
sends each basis vector `single i 1` into the span of the basis vectors of strictly smaller
weight, then every vector is killed by a power of `f`. -/
theorem Module.End.exists_pow_apply_eq_zero_of_forall_mem_support_lt
    (f : Module.End R (ι →₀ R)) (w : ι → α) (hw : WellFounded (InvImage (· < ·) w))
    (hf : ∀ i, ∀ j ∈ (f (single i 1)).support, w j < w i) (x : ι →₀ R) :
    ∃ k, (f ^ k) x = 0 := by
  let N : Submodule R (ι →₀ R) :=
    { carrier := {x | ∃ k, (f ^ k) x = 0}
      add_mem' := by
        rintro x y ⟨a, ha⟩ ⟨b, hb⟩
        refine ⟨max a b, ?_⟩
        rw [map_add, Module.End.pow_map_zero_of_le (le_max_left _ _) ha,
          Module.End.pow_map_zero_of_le (le_max_right _ _) hb, add_zero]
      zero_mem' := ⟨0, map_zero _⟩
      smul_mem' := by
        rintro c x ⟨a, ha⟩
        exact ⟨a, by rw [map_smul, ha, smul_zero]⟩ }
  have hN : ∀ x, x ∈ N ↔ ∃ k, (f ^ k) x = 0 := fun _ ↦ Iff.rfl
  -- Well-founded induction on the weight: `f (single i 1)` involves only basis vectors of
  -- smaller weight, each of which is killed by a power of `f` by induction.
  have hsingle : ∀ i, single i (1 : R) ∈ N := by
    intro i
    induction i using hw.induction with
    | _ i ih =>
      have hfi : f (single i 1) ∈ N := by
        rw [← Finsupp.sum_single (f (single i 1))]
        refine Submodule.sum_mem _ fun j hj ↦ ?_
        rw [← Finsupp.smul_single_one]
        exact N.smul_mem _ (ih j (hf i j hj))
      obtain ⟨k, hk⟩ := (hN _).1 hfi
      exact (hN _).2 ⟨k + 1, by rw [pow_succ, Module.End.mul_apply, hk]⟩
  have hx : x ∈ N := by
    induction x using Finsupp.induction_linear with
    | zero => exact N.zero_mem
    | add x y hx hy => exact N.add_mem hx hy
    | single i c =>
      rw [← Finsupp.smul_single_one]
      exact N.smul_mem _ (hsingle i)
  exact (hN x).1 hx

end Finsupp

section Family

namespace Module.End

variable {R M N ι : Type*} [Semiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N]

/-- The submodule of vectors killed by every composite `f i₁ ∘ ⋯ ∘ f i_d` of `d` members of a
family `f` of endomorphisms (`Module.End.mem_wordKer_iff`). Only `0` is killed by the empty
composite, and `x` is killed by all composites of length `d + 1` exactly when every `f i x` is
killed by all composites of length `d` (`Module.End.mem_wordKer_succ`).

These submodules increase with `d` (`Module.End.monotone_wordKer`). The family is *locally
nilpotent* when they exhaust the module, `⨆ d, wordKer f d = ⊤`: every vector is killed by all
sufficiently long composites (`Module.End.iSup_wordKer_eq_top_iff`). -/
def wordKer (f : ι → Module.End R M) : ℕ → Submodule R M
  | 0 => ⊥
  | d + 1 => ⨅ i, (wordKer f d).comap (f i)

variable (f : ι → Module.End R M)

/-- Only `0` is killed by the empty composite. -/
@[simp]
theorem wordKer_zero : wordKer f 0 = ⊥ :=
  (rfl)

/-- The recursive description of `wordKer f (d + 1)`. -/
theorem wordKer_succ (d : ℕ) : wordKer f (d + 1) = ⨅ i, (wordKer f d).comap (f i) :=
  (rfl)

/-- A vector is killed by all composites of length `d + 1` exactly when its image under every
member of the family is killed by all composites of length `d`. -/
@[simp]
theorem mem_wordKer_succ {d : ℕ} {x : M} : x ∈ wordKer f (d + 1) ↔ ∀ i, f i x ∈ wordKer f d := by
  simp only [wordKer_succ, Submodule.mem_iInf, Submodule.mem_comap]

/-- A vector lies in `wordKer f d` exactly when it is killed by the composite of every word of
length `d` in the family `f`. -/
theorem mem_wordKer_iff {d : ℕ} {x : M} :
    x ∈ wordKer f d ↔ ∀ w : List ι, w.length = d → (w.map f).prod x = 0 := by
  induction d generalizing x with
  | zero => simp [List.length_eq_zero_iff]
  | succ d ih =>
    simp only [mem_wordKer_succ, ih]
    refine ⟨fun h w hw ↦ ?_, fun h i w hw ↦ ?_⟩
    · obtain rfl | ⟨w, i, rfl⟩ := w.eq_nil_or_concat
      · simp at hw
      · simp only [List.concat_eq_append, List.length_append, List.length_singleton,
          Nat.add_right_cancel_iff] at hw
        simpa [Module.End.mul_apply] using h i w hw
    · simpa [Module.End.mul_apply] using h (w ++ [i]) (by simp [hw])

/-- A vector killed by all composites of length `d` is killed by all longer composites. -/
theorem monotone_wordKer : Monotone (wordKer f) := by
  refine monotone_nat_of_le_succ fun d ↦ ?_
  induction d with
  | zero => exact bot_le
  | succ d ih => exact iInf_mono fun i ↦ Submodule.comap_mono ih

/-- The family `f` is locally nilpotent, `⨆ d, wordKer f d = ⊤`, exactly when every vector is
killed by all composites of some length. -/
theorem iSup_wordKer_eq_top_iff : ⨆ d, wordKer f d = ⊤ ↔ ∀ x, ∃ d, x ∈ wordKer f d := by
  simp only [Submodule.eq_top_iff', Submodule.mem_iSup_of_directed _
    (monotone_wordKer f).directed_le]

/-- If no nonzero vector is killed by every member of the family, then no nonzero vector is killed
by all composites of a given length. -/
theorem wordKer_eq_bot_of_iInf_ker_eq_bot (hf : ⨅ i, LinearMap.ker (f i) = ⊥) (d : ℕ) :
    wordKer f d = ⊥ := by
  induction d with
  | zero => exact wordKer_zero f
  | succ d ih => simp only [wordKer_succ, ih, Submodule.comap_bot, hf]

/-- For a nonempty family all of whose members equal `g`, `wordKer` is the kernel of `g ^ d`. -/
theorem wordKer_const [Nonempty ι] (g : Module.End R M) (d : ℕ) :
    wordKer (fun _ : ι ↦ g) d = LinearMap.ker (g ^ d) := by
  induction d with
  | zero => rw [wordKer_zero, pow_zero, Module.End.one_eq_id, LinearMap.ker_id]
  | succ d ih => rw [wordKer_succ, ih, iInf_const, pow_succ, Module.End.mul_eq_comp,
      LinearMap.ker_comp]

variable {f} {f' : ι → Module.End R N} {g : M →ₗ[R] N}

/-- A linear map intertwining two families of endomorphisms maps `wordKer f d` into
`wordKer f' d`. -/
theorem map_wordKer_le (hg : ∀ i, g ∘ₗ f i = f' i ∘ₗ g) (d : ℕ) :
    (wordKer f d).map g ≤ wordKer f' d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_wordKer_succ] at hx
    rw [mem_wordKer_succ]
    intro i
    rw [← LinearMap.comp_apply, ← hg i, LinearMap.comp_apply]
    exact ih (Submodule.mem_map_of_mem (hx i))

/-- An injective linear map intertwining two families of endomorphisms pulls `wordKer f' d` back to
`wordKer f d`. -/
theorem comap_wordKer_of_injective (hg : ∀ i, g ∘ₗ f i = f' i ∘ₗ g)
    (hinj : Function.Injective g) (d : ℕ) : (wordKer f' d).comap g = wordKer f d := by
  induction d with
  | zero => simpa using LinearMap.ker_eq_bot_of_injective hinj
  | succ d ih =>
    ext x
    simp only [Submodule.mem_comap, mem_wordKer_succ]
    refine forall_congr' fun i ↦ ?_
    rw [← ih, Submodule.mem_comap, ← LinearMap.comp_apply g, hg i, LinearMap.comp_apply]

/-- Local nilpotence passes to quotients: the image of a locally nilpotent family under a
surjective intertwining linear map is locally nilpotent. -/
theorem iSup_wordKer_eq_top_of_surjective (hg : ∀ i, g ∘ₗ f i = f' i ∘ₗ g)
    (hsurj : Function.Surjective g) (hf : ⨆ d, wordKer f d = ⊤) : ⨆ d, wordKer f' d = ⊤ := by
  rw [eq_top_iff, ← LinearMap.range_eq_top.2 hsurj, LinearMap.range_eq_map, ← hf,
    Submodule.map_iSup]
  exact iSup_mono (map_wordKer_le hg)

/-- Local nilpotence passes to submodules: a family intertwined by an injective linear map with a
locally nilpotent family is locally nilpotent. -/
theorem iSup_wordKer_eq_top_of_injective (hg : ∀ i, g ∘ₗ f i = f' i ∘ₗ g)
    (hinj : Function.Injective g) (hf' : ⨆ d, wordKer f' d = ⊤) : ⨆ d, wordKer f d = ⊤ := by
  rw [iSup_wordKer_eq_top_iff] at hf' ⊢
  intro x
  obtain ⟨d, hd⟩ := hf' (g x)
  exact ⟨d, comap_wordKer_of_injective hg hinj d ▸ hd⟩

end Module.End

end Family
