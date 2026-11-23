/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import MathlibExt.RingTheory.Ideal.PrimeExtension

/-!
# Prime ideals away from a denominator-clearing ideal

Let `O → B` be an injective algebra map of commutative rings with `B` a
Dedekind domain, and let `𝔠 : Ideal O` be an ideal whose elements clear
denominators uniformly (`algebraMap O B c * b` is in the range of
`algebraMap O B` for all `b : B`), nonzero, and comaximal with every nonzero
prime of `O` it is not contained in. Then contraction and extension give an
equivalence between all primes of `B` not containing `𝔠.map f` and all primes
of `O` not containing `𝔠`, including the zero prime. The equivalence on
nonzero primes is its restriction.

This is ATLAS `NumberTheoryI` Corollary 6.27: for an order `O` with integral
closure `B` and conductor `𝔠`, the restriction of `Spec B → Spec O` to prime
ideals not containing `𝔠` is a bijection with inverse `𝔭 ↦ 𝔭B`. Here `𝔠` is
any ideal satisfying the conductor hypotheses, rather than the conductor
itself. The primality of the extended ideals (Lemma 6.26 of the book) is the
already-ported `Ideal.isPrime_map_of_coprime_clearDenom` in
`MathlibExt/RingTheory/Ideal/PrimeExtension.lean`; the new content is the
contraction/extension round-trip and the equivalence.
-/

@[expose] public section

namespace Ideal

/-- Denominator clearing for one span element, iterated: if `x` lies in the
extended ideal `𝔭.map f` and `s ∈ 𝔠`, then some power of `f s` times `x` is
the image of an element of `𝔭`. -/
private lemma conductor_span_helper
    {O B : Type*} [CommRing O] [CommRing B] [Algebra O B]
    {𝔠 𝔭 : Ideal O}
    (hclear : ∀ c ∈ 𝔠, ∀ b : B,
      algebraMap O B c * b ∈ Set.range (algebraMap O B))
    {s : O} (hs : s ∈ 𝔠)
    {x : B} (hx : x ∈ 𝔭.map (algebraMap O B)) :
    ∃ n : ℕ, ∃ q ∈ 𝔭, algebraMap O B q =
      (algebraMap O B s) ^ n * x := by
  set f := algebraMap O B with hf_def
  change x ∈ Ideal.span (f '' ↑𝔭) at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨p, hp, rfl⟩ := hy
    exact ⟨0, p, hp, by simp⟩
  | zero => exact ⟨0, 0, 𝔭.zero_mem, by simp⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨nx, qx, hqx, hfqx⟩ := ihx
    obtain ⟨ny, qy, hqy, hfqy⟩ := ihy
    refine ⟨max nx ny,
      s ^ (max nx ny - nx) * qx + s ^ (max nx ny - ny) * qy,
      𝔭.add_mem (𝔭.mul_mem_left _ hqx) (𝔭.mul_mem_left _ hqy), ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, hfqx, hfqy, mul_add]
    congr 1
    · rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (le_max_left nx ny)]
    · rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (le_max_right nx ny)]
  | smul b x _ ihx =>
    obtain ⟨n, q, hq, hfq⟩ := ihx
    obtain ⟨r, hr⟩ := hclear s hs b
    refine ⟨n + 1, r * q, 𝔭.mul_mem_left r hq, ?_⟩
    simp only [map_mul, pow_succ, smul_eq_mul]
    rw [hfq, hr]
    ring

/-- Contraction after extension is the identity on primes not containing `𝔠`. -/
lemma comap_map_eq_of_not_le_conductor
    {O B : Type*} [CommRing O] [CommRing B] [Algebra O B]
    {𝔠 𝔭 : Ideal O}
    (hf : Function.Injective (algebraMap O B))
    (hclear : ∀ c ∈ 𝔠, ∀ b : B,
      algebraMap O B c * b ∈ Set.range (algebraMap O B))
    (h𝔭 : 𝔭.IsPrime) (h𝔭_nc : ¬ 𝔠 ≤ 𝔭) :
    Ideal.comap (algebraMap O B) (Ideal.map (algebraMap O B) 𝔭) = 𝔭 := by
  apply le_antisymm
  · intro a ha
    obtain ⟨s, hs, hs𝔭⟩ := Set.not_subset.mp h𝔭_nc
    obtain ⟨n, q, hq, hfq⟩ :=
      conductor_span_helper hclear hs (show algebraMap O B a ∈
        Ideal.map (algebraMap O B) 𝔭 from ha)
    have h_eq : q = s ^ n * a := hf (by rw [map_mul, map_pow, hfq])
    rw [h_eq] at hq
    exact (h𝔭.mem_or_mem hq).resolve_left
      (mt (Ideal.IsPrime.mem_of_pow_mem h𝔭 n) hs𝔭)
  · exact Ideal.le_comap_map

/-- Contraction of a nonzero ideal is nonzero when `𝔠` is nonzero: a
nonzero element of `𝔠` clears a nonzero element of `𝔮` back to a nonzero
element of the contraction. -/
lemma comap_ne_bot_of_ne_bot
    {O B : Type*} [CommRing O] [CommRing B] [IsDedekindDomain B] [Algebra O B]
    {𝔠 : Ideal O}
    (hf : Function.Injective (algebraMap O B))
    (hclear : ∀ c ∈ 𝔠, ∀ b : B,
      algebraMap O B c * b ∈ Set.range (algebraMap O B))
    (h𝔠_ne : 𝔠 ≠ ⊥)
    {𝔮 : Ideal B} (h𝔮_ne : 𝔮 ≠ ⊥) :
    Ideal.comap (algebraMap O B) 𝔮 ≠ ⊥ := by
  intro h_bot
  have ⟨c, hc, hc_ne⟩ : ∃ c ∈ 𝔠, c ≠ 0 := by
    by_contra h
    push Not at h
    exact h𝔠_ne (eq_bot_iff.mpr fun x hx => by simpa using h x hx)
  have ⟨b, hb, hb_ne⟩ : ∃ b ∈ 𝔮, b ≠ 0 := by
    by_contra h
    push Not at h
    exact h𝔮_ne (eq_bot_iff.mpr fun x hx => by simpa using h x hx)
  obtain ⟨a, ha⟩ := hclear c hc b
  have hmem : a ∈ Ideal.comap (algebraMap O B) 𝔮 := by
    rw [Ideal.mem_comap, ha]
    exact 𝔮.mul_mem_left _ hb
  rw [h_bot] at hmem
  have ha0 : a = 0 := Ideal.mem_bot.mp hmem
  rw [ha0, map_zero] at ha
  exact hb_ne ((mul_eq_zero.mp ha.symm).resolve_left
    fun h => hc_ne (hf (by simpa using h)))

/-- Extension after contraction is the identity on primes of `B` not
containing `𝔠.map f`, using that `B` has Krull dimension at most one. -/
lemma map_comap_eq_of_not_le_map_conductor
    {O B : Type*} [CommRing O] [CommRing B] [IsDedekindDomain B] [Algebra O B]
    {𝔠 : Ideal O}
    (hf : Function.Injective (algebraMap O B))
    (hclear : ∀ c ∈ 𝔠, ∀ b : B,
      algebraMap O B c * b ∈ Set.range (algebraMap O B))
    (h𝔠_ne : 𝔠 ≠ ⊥)
    (hsup : ∀ (𝔭 : Ideal O), 𝔭.IsPrime → 𝔭 ≠ ⊥ → ¬ 𝔠 ≤ 𝔭 → 𝔠 ⊔ 𝔭 = ⊤)
    {𝔮 : Ideal B} (h𝔮 : 𝔮.IsPrime) (h𝔮_ne : 𝔮 ≠ ⊥)
    (h𝔮_nc : ¬ 𝔠.map (algebraMap O B) ≤ 𝔮) :
    Ideal.map (algebraMap O B) (Ideal.comap (algebraMap O B) 𝔮) = 𝔮 := by
  have : (Ideal.comap (algebraMap O B) 𝔮).IsPrime := Ideal.comap_isPrime _ _
  have h𝔭_nc : ¬ 𝔠 ≤ Ideal.comap (algebraMap O B) 𝔮 :=
    fun h => h𝔮_nc (Ideal.map_le_of_le_comap h)
  have h𝔭_ne : Ideal.comap (algebraMap O B) 𝔮 ≠ ⊥ := comap_ne_bot_of_ne_bot
    hf hclear h𝔠_ne h𝔮_ne
  have : (Ideal.map (algebraMap O B)
      (Ideal.comap (algebraMap O B) 𝔮)).IsPrime :=
    Ideal.isPrime_map_of_coprime_clearDenom _ _ inferInstance hf hclear
      (hsup _ inferInstance h𝔭_ne h𝔭_nc)
  have hP0 : Ideal.map (algebraMap O B)
      (Ideal.comap (algebraMap O B) 𝔮) ≠ ⊥ := by
    rw [Ne, Ideal.map_eq_bot_iff_of_injective hf]
    exact h𝔭_ne
  exact (Ring.DimensionLeOne.prime_le_prime_iff_eq hP0).mp Ideal.map_comap_le

/-- Contraction and extension give an equivalence between all primes of `B`
not containing `𝔠.map (algebraMap O B)` and all primes of `O` not containing
`𝔠`, including the zero prime on both sides. This restores the full spectra
in ATLAS `NumberTheoryI` Corollary 6.27. -/
noncomputable def primeEquivOfNotLeConductor
    {O B : Type*} [CommRing O] [CommRing B] [IsDedekindDomain B] [Algebra O B]
    (hf : Function.Injective (algebraMap O B))
    (𝔠 : Ideal O) (h𝔠_ne : 𝔠 ≠ ⊥)
    (hclear : ∀ c ∈ 𝔠, ∀ b : B,
      algebraMap O B c * b ∈ Set.range (algebraMap O B))
    (hsup : ∀ (𝔭 : Ideal O), 𝔭.IsPrime → 𝔭 ≠ ⊥ → ¬ 𝔠 ≤ 𝔭 → 𝔠 ⊔ 𝔭 = ⊤) :
    {𝔮 : Ideal B // 𝔮.IsPrime ∧ ¬ (𝔠.map (algebraMap O B) ≤ 𝔮)} ≃
      {𝔭 : Ideal O // 𝔭.IsPrime ∧ ¬ 𝔠 ≤ 𝔭} := by
  classical
  exact
    { toFun := fun 𝔮 =>
        ⟨𝔮.1.comap (algebraMap O B), 𝔮.2.1.comap (algebraMap O B),
          fun h => 𝔮.2.2 (Ideal.map_le_of_le_comap h)⟩
      invFun := fun 𝔭 =>
        ⟨𝔭.1.map (algebraMap O B), (by
          by_cases h𝔭_bot : 𝔭.1 = ⊥
          · rw [h𝔭_bot, Ideal.map_bot]
            infer_instance
          · exact Ideal.isPrime_map_of_coprime_clearDenom _ _ 𝔭.2.1 hf hclear
              (hsup 𝔭.1 𝔭.2.1 h𝔭_bot 𝔭.2.2)), (by
          rw [Ideal.map_le_iff_le_comap,
            comap_map_eq_of_not_le_conductor hf hclear 𝔭.2.1 𝔭.2.2]
          exact 𝔭.2.2)⟩
      left_inv := fun 𝔮 => Subtype.ext (by
        change Ideal.map (algebraMap O B) (Ideal.comap (algebraMap O B) 𝔮.1) = 𝔮.1
        by_cases h𝔮_bot : 𝔮.1 = ⊥
        · rw [h𝔮_bot]
          exact Ideal.map_comap_bot (f := algebraMap O B)
        · exact map_comap_eq_of_not_le_map_conductor hf hclear h𝔠_ne hsup
            𝔮.2.1 h𝔮_bot 𝔮.2.2)
      right_inv := fun 𝔭 =>
        Subtype.ext (comap_map_eq_of_not_le_conductor hf hclear 𝔭.2.1 𝔭.2.2) }

@[simp]
theorem primeEquivOfNotLeConductor_apply
    {O B : Type*} [CommRing O] [CommRing B] [IsDedekindDomain B] [Algebra O B]
    (hf : Function.Injective (algebraMap O B))
    (𝔠 : Ideal O) (h𝔠_ne : 𝔠 ≠ ⊥)
    (hclear : ∀ c ∈ 𝔠, ∀ b : B,
      algebraMap O B c * b ∈ Set.range (algebraMap O B))
    (hsup : ∀ (𝔭 : Ideal O), 𝔭.IsPrime → 𝔭 ≠ ⊥ → ¬ 𝔠 ≤ 𝔭 → 𝔠 ⊔ 𝔭 = ⊤)
    (𝔮 : {𝔮 : Ideal B // 𝔮.IsPrime ∧ ¬ (𝔠.map (algebraMap O B) ≤ 𝔮)}) :
    (primeEquivOfNotLeConductor hf 𝔠 h𝔠_ne hclear hsup 𝔮).1 =
      𝔮.1.comap (algebraMap O B) := by
  rfl

@[simp]
theorem primeEquivOfNotLeConductor_symm_apply
    {O B : Type*} [CommRing O] [CommRing B] [IsDedekindDomain B] [Algebra O B]
    (hf : Function.Injective (algebraMap O B))
    (𝔠 : Ideal O) (h𝔠_ne : 𝔠 ≠ ⊥)
    (hclear : ∀ c ∈ 𝔠, ∀ b : B,
      algebraMap O B c * b ∈ Set.range (algebraMap O B))
    (hsup : ∀ (𝔭 : Ideal O), 𝔭.IsPrime → 𝔭 ≠ ⊥ → ¬ 𝔠 ≤ 𝔭 → 𝔠 ⊔ 𝔭 = ⊤)
    (𝔭 : {𝔭 : Ideal O // 𝔭.IsPrime ∧ ¬ 𝔠 ≤ 𝔭}) :
    ((primeEquivOfNotLeConductor hf 𝔠 h𝔠_ne hclear hsup).symm 𝔭).1 =
      𝔭.1.map (algebraMap O B) := by
  rfl

/-- Contraction and extension give an equivalence between the nonzero primes
of `B` not containing `𝔠.map (algebraMap O B)` and the nonzero primes of `O`
not containing `𝔠`. This is the restriction of
`Ideal.primeEquivOfNotLeConductor` to nonzero prime ideals. -/
noncomputable def primeEquivOfCoprimeConductor
    {O B : Type*} [CommRing O] [CommRing B] [IsDedekindDomain B] [Algebra O B]
    (hf : Function.Injective (algebraMap O B))
    (𝔠 : Ideal O) (h𝔠_ne : 𝔠 ≠ ⊥)
    (hclear : ∀ c ∈ 𝔠, ∀ b : B,
      algebraMap O B c * b ∈ Set.range (algebraMap O B))
    (hsup : ∀ (𝔭 : Ideal O), 𝔭.IsPrime → 𝔭 ≠ ⊥ → ¬ 𝔠 ≤ 𝔭 → 𝔠 ⊔ 𝔭 = ⊤) :
    {𝔮 : Ideal B // 𝔮.IsPrime ∧ 𝔮 ≠ ⊥ ∧ ¬ (𝔠.map (algebraMap O B) ≤ 𝔮)} ≃
      {𝔭 : Ideal O // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ 𝔠 ≤ 𝔭} :=
  let e := primeEquivOfNotLeConductor hf 𝔠 h𝔠_ne hclear hsup
  { toFun := fun 𝔮 =>
      ⟨𝔮.1.comap (algebraMap O B), 𝔮.2.1.comap (algebraMap O B),
        comap_ne_bot_of_ne_bot hf hclear h𝔠_ne 𝔮.2.2.1,
        fun h => 𝔮.2.2.2 (Ideal.map_le_of_le_comap h)⟩
    invFun := fun 𝔭 =>
      ⟨𝔭.1.map (algebraMap O B),
        Ideal.isPrime_map_of_coprime_clearDenom _ _ 𝔭.2.1 hf hclear
          (hsup 𝔭.1 𝔭.2.1 𝔭.2.2.1 𝔭.2.2.2),
        by rw [Ne, Ideal.map_eq_bot_iff_of_injective hf]; exact 𝔭.2.2.1,
        (by
          rw [Ideal.map_le_iff_le_comap,
            comap_map_eq_of_not_le_conductor hf hclear 𝔭.2.1 𝔭.2.2.2]
          exact 𝔭.2.2.2)⟩
    left_inv := fun 𝔮 =>
      Subtype.ext (congrArg
        (fun (𝔮 : {𝔮 : Ideal B // 𝔮.IsPrime ∧ ¬ 𝔠.map (algebraMap O B) ≤ 𝔮}) => 𝔮.1)
        (e.symm_apply_apply ⟨𝔮.1, 𝔮.2.1, 𝔮.2.2.2⟩))
    right_inv := fun 𝔭 =>
      Subtype.ext (congrArg (fun (𝔭 : {𝔭 : Ideal O // 𝔭.IsPrime ∧ ¬ 𝔠 ≤ 𝔭}) => 𝔭.1)
        (e.apply_symm_apply ⟨𝔭.1, 𝔭.2.1, 𝔭.2.2.2⟩)) }

@[simp]
theorem primeEquivOfCoprimeConductor_apply
    {O B : Type*} [CommRing O] [CommRing B] [IsDedekindDomain B] [Algebra O B]
    (hf : Function.Injective (algebraMap O B))
    (𝔠 : Ideal O) (h𝔠_ne : 𝔠 ≠ ⊥)
    (hclear : ∀ c ∈ 𝔠, ∀ b : B,
      algebraMap O B c * b ∈ Set.range (algebraMap O B))
    (hsup : ∀ (𝔭 : Ideal O), 𝔭.IsPrime → 𝔭 ≠ ⊥ → ¬ 𝔠 ≤ 𝔭 → 𝔠 ⊔ 𝔭 = ⊤)
    (𝔮 : {𝔮 : Ideal B // 𝔮.IsPrime ∧ 𝔮 ≠ ⊥ ∧
      ¬ (𝔠.map (algebraMap O B) ≤ 𝔮)}) :
    (primeEquivOfCoprimeConductor hf 𝔠 h𝔠_ne hclear hsup 𝔮).1 =
      𝔮.1.comap (algebraMap O B) := by
  rfl

@[simp]
theorem primeEquivOfCoprimeConductor_symm_apply
    {O B : Type*} [CommRing O] [CommRing B] [IsDedekindDomain B] [Algebra O B]
    (hf : Function.Injective (algebraMap O B))
    (𝔠 : Ideal O) (h𝔠_ne : 𝔠 ≠ ⊥)
    (hclear : ∀ c ∈ 𝔠, ∀ b : B,
      algebraMap O B c * b ∈ Set.range (algebraMap O B))
    (hsup : ∀ (𝔭 : Ideal O), 𝔭.IsPrime → 𝔭 ≠ ⊥ → ¬ 𝔠 ≤ 𝔭 → 𝔠 ⊔ 𝔭 = ⊤)
    (𝔭 : {𝔭 : Ideal O // 𝔭.IsPrime ∧ 𝔭 ≠ ⊥ ∧ ¬ 𝔠 ≤ 𝔭}) :
    ((primeEquivOfCoprimeConductor hf 𝔠 h𝔠_ne hclear hsup).symm 𝔭).1 =
      𝔭.1.map (algebraMap O B) := by
  rfl

end Ideal
