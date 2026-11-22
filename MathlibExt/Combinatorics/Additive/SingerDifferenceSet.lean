/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Singer's cyclic difference-set theorem, via the classical projective-plane
argument: a 2-dimensional subspace of a degree-3 field extension picks out a
`(q + 1)`-element difference set in `ZMod (q ^ 2 + q + 1)`.
-/

module

public import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Algebra.Basic
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.IsPrimePow
import Mathlib.Algebra.Module.Submodule.Lattice
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.FieldTheory.Finiteness
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.FieldTheory.IntermediateField.Algebraic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Defs
import Mathlib.RingTheory.SimpleRing.Basic

/-!
# Singer's cyclic difference-set theorem

Source: Harri Haanpää, *Minimum Sum and Difference Covers of Abelian Groups*,
Journal of Integer Sequences 7 (2004), Article 04.2.6,
<https://cs.uwaterloo.ca/journals/JIS/VOL7/Haanpaa/haanpaa.tex>,
difference-set definition and Singer prime-power construction, lines 209–215.

For `q` a prime power, there is a `(q + 1)`-element subset `D` of the cyclic
group `ZMod (q ^ 2 + q + 1)` in which every nonzero element is uniquely an
ordered difference of two members of `D`, via the classical projective-plane
argument over the degree-3 extension of the field with `q` elements.
-/

open scoped IntermediateField

namespace MetaMathlibExt

section SingerPrivate

variable {K L : Type*} [Field K] [Field L] [Fintype K] [Fintype L] [Algebra K L]

omit [Algebra K L] in
/-- A finite field has at least two elements. -/
private lemma sgN2_two_le {q : ℕ} (hqK : Fintype.card K = q) : 2 ≤ q := by
  classical
  have h := Fintype.one_lt_card (α := K)
  omega

/-- The degree-3 extension has `q ^ 3` elements. -/
private lemma sgN2_cardL {q : ℕ} (hqK : Fintype.card K = q)
    (hfr : Module.finrank K L = 3) : Fintype.card L = q ^ 3 := by
  classical
  have h := Module.card_eq_pow_finrank (K := K) (V := L)
  rw [hfr, hqK] at h
  exact h

omit [Algebra K L] in
/-- The unit group of `K` has one fewer element than `K`. -/
private lemma sgN2_cardKu {q : ℕ} [DecidableEq K] (hqK : Fintype.card K = q) :
    Fintype.card Kˣ + 1 = q := by
  classical
  have h := Fintype.card_eq_card_units_add_one K
  omega

omit [Algebra K L] in
/-- `|Kˣ| * N = |Lˣ|` where `N = q ^ 2 + q + 1`. -/
private lemma sgN2_mul {q : ℕ} [DecidableEq K] [DecidableEq L]
    (hqK : Fintype.card K = q) (hcardL : Fintype.card L = q ^ 3) :
    Fintype.card Kˣ * (q ^ 2 + q + 1) = Fintype.card Lˣ := by
  classical
  have hK := sgN2_cardKu hqK
  have hL : Fintype.card Lˣ + 1 = q ^ 3 := by
    have h := Fintype.card_eq_card_units_add_one L
    omega
  have hq : q = Fintype.card Kˣ + 1 := by omega
  have key : Fintype.card Kˣ * (q ^ 2 + q + 1) + 1 = q ^ 3 := by rw [hq]; ring
  omega

omit [Fintype L] in
omit [Algebra K L] in
/-- Every nonzero element of `L` is a natural-number power of the generator. -/
private lemma sgN3 [Finite L] (g : Lˣ) (hg : ∀ x : Lˣ, x ∈ Subgroup.zpowers g) :
    ∀ y : L, y ≠ 0 → ∃ k : ℕ, (g : L) ^ k = y := by
  classical
  intro y hy
  have hmem := hg (Units.mk0 y hy)
  rw [← mem_powers_iff_mem_zpowers, Submonoid.mem_powers_iff] at hmem
  obtain ⟨k, hk⟩ := hmem
  refine ⟨k, ?_⟩
  have hcongr := congrArg Units.val hk
  rw [Units.val_pow_eq_pow_val, Units.val_mk0] at hcongr
  exact hcongr

omit [Fintype L] in
/-- `γ ^ k` lies in `K` iff `N` divides `k`. -/
private lemma sgN4 {q : ℕ} [Finite L]
    (hqK : Fintype.card K = q) (hfr : Module.finrank K L = 3)
    (g : Lˣ) (hg : ∀ x : Lˣ, x ∈ Subgroup.zpowers g) (k : ℕ) :
    (g : L) ^ k ∈ Set.range (algebraMap K L) ↔ (q ^ 2 + q + 1) ∣ k := by
  classical
  have : Fintype L := Fintype.ofFinite L
  have hKq := sgN2_cardKu hqK
  have hcardL := sgN2_cardL hqK hfr
  have hmul := sgN2_mul hqK hcardL
  have hKpos : 0 < Fintype.card Kˣ := by
    have h2 := sgN2_two_le hqK
    omega
  have halg_inj : Function.Injective (algebraMap K L) := RingHom.injective _
  have hord : orderOf g = Fintype.card Lˣ := by
    have h := orderOf_eq_card_of_forall_mem_zpowers hg
    rwa [Nat.card_eq_fintype_card] at h
  set e : Kˣ →* Lˣ := Units.map (algebraMap K L)
  have he_inj : Function.Injective e := by
    intro c d hcd
    have hval : algebraMap K L (c : K) = algebraMap K L (d : K) :=
      congrArg Units.val hcd
    exact Units.ext (halg_inj hval)
  have himg_sub : Finset.image e Finset.univ ⊆
      Finset.univ.filter (fun y : Lˣ => y ^ Fintype.card Kˣ = 1) := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨c, _, rfl⟩ := hy
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have h1 : e c ^ Fintype.card Kˣ = e (c ^ Fintype.card Kˣ) := (map_pow e c _).symm
    rw [h1, pow_card_eq_one, map_one]
  have himg_card : (Finset.image e Finset.univ).card = Fintype.card Kˣ := by
    rw [Finset.card_image_of_injective _ he_inj, Finset.card_univ]
  have hS_card : (Finset.univ.filter (fun y : Lˣ => y ^ Fintype.card Kˣ = 1)).card
      ≤ Fintype.card Kˣ :=
    IsCyclic.card_pow_eq_one_le (α := Lˣ) hKpos
  have heq : Finset.image e Finset.univ =
      Finset.univ.filter (fun y : Lˣ => y ^ Fintype.card Kˣ = 1) :=
    Finset.eq_of_subset_of_card_le himg_sub (by rw [himg_card]; exact hS_card)
  have hchar : ∀ y : Lˣ, (∃ c : Kˣ, e c = y) ↔ y ^ Fintype.card Kˣ = 1 := by
    intro y
    constructor
    · rintro ⟨c, hc⟩
      have hmem : y ∈ Finset.image e Finset.univ :=
        Finset.mem_image.mpr ⟨c, Finset.mem_univ c, hc⟩
      rw [heq] at hmem
      exact (Finset.mem_filter.mp hmem).2
    · intro hy
      have hmem : y ∈ Finset.image e Finset.univ := by
        rw [heq]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ y, hy⟩
      obtain ⟨c, _, hc⟩ := Finset.mem_image.mp hmem
      exact ⟨c, hc⟩
  have hmem : ∀ y : Lˣ, (y : L) ∈ Set.range (algebraMap K L) ↔
      y ^ Fintype.card Kˣ = 1 := by
    intro y
    rw [← hchar y]
    constructor
    · rintro ⟨c, hc⟩
      have hc0 : c ≠ 0 := by
        intro hz
        rw [hz, map_zero] at hc
        exact Units.ne_zero y hc.symm
      refine ⟨Units.mk0 c hc0, Units.ext ?_⟩
      change algebraMap K L ((Units.mk0 c hc0 : Kˣ) : K) = (y : L)
      rw [show ((Units.mk0 c hc0 : Kˣ) : K) = c from rfl]
      exact hc
    · rintro ⟨c, hc⟩
      exact ⟨(c : K), congrArg Units.val hc⟩
  have hkk : ((g ^ k : Lˣ) : L) = (g : L) ^ k := Units.val_pow_eq_pow_val g k
  rw [← hkk, hmem (g ^ k), ← pow_mul, ← orderOf_dvd_iff_pow_eq_one, hord, ← hmul,
    mul_comm k (Fintype.card Kˣ)]
  exact mul_dvd_mul_iff_left (ne_of_gt hKpos)

omit [Fintype L] in
/-- Membership of `γ ^ k` in `W` depends only on `k % N`. -/
private lemma sgN5 {q : ℕ} [Finite L]
    (hqK : Fintype.card K = q) (hfr : Module.finrank K L = 3)
    (g : Lˣ) (hg : ∀ x : Lˣ, x ∈ Subgroup.zpowers g)
    (W : Submodule K L) (k : ℕ) :
    (g : L) ^ k ∈ W ↔ (g : L) ^ (k % (q ^ 2 + q + 1)) ∈ W := by
  classical
  have hdvd : (q ^ 2 + q + 1) ∣ (q ^ 2 + q + 1) * (k / (q ^ 2 + q + 1)) :=
    dvd_mul_right _ _
  obtain ⟨c, hc⟩ := (sgN4 hqK hfr g hg _).mpr hdvd
  have hg0 : (g : L) ≠ 0 := Units.ne_zero g
  have hpow0 : (g : L) ^ ((q ^ 2 + q + 1) * (k / (q ^ 2 + q + 1))) ≠ 0 :=
    pow_ne_zero _ hg0
  have hc0 : c ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hc
    exact hpow0 hc.symm
  have hdecomp : (g : L) ^ k
      = algebraMap K L c * (g : L) ^ (k % (q ^ 2 + q + 1)) := by
    conv_lhs => rw [← Nat.div_add_mod k (q ^ 2 + q + 1), pow_add]
    rw [← hc]
  have hsmul : algebraMap K L c * (g : L) ^ (k % (q ^ 2 + q + 1))
      = c • ((g : L) ^ (k % (q ^ 2 + q + 1))) := (Algebra.smul_def c _).symm
  rw [hdecomp, hsmul]
  exact Submodule.smul_mem_iff W hc0

omit [Fintype L] in
/-- Corollary: shifting the exponent by `x.val` matches addition in `ZMod N`. -/
private lemma sgN5cor {q : ℕ} [Finite L]
    (hqK : Fintype.card K = q) (hfr : Module.finrank K L = 3)
    (g : Lˣ) (hg : ∀ x : Lˣ, x ∈ Subgroup.zpowers g)
    (W : Submodule K L) (i x : ZMod (q ^ 2 + q + 1)) :
    (g : L) ^ ((i + x).val) ∈ W ↔ (g : L) ^ (x.val + i.val) ∈ W := by
  classical
  have : NeZero (q ^ 2 + q + 1) := ⟨by positivity⟩
  have hmod : (x.val + i.val) % (q ^ 2 + q + 1) = (i + x).val := by
    rw [add_comm x.val i.val, ← ZMod.val_add]
  have h2 := sgN5 hqK hfr g hg W (x.val + i.val)
  rw [hmod] at h2
  exact h2.symm

omit [Fintype K] [Fintype L] in
/-- The trace of `W` in `ZMod N`: indices `i` with `γ ^ i.val ∈ W`. -/
private noncomputable def sgT (q : ℕ) (g : Lˣ) (W : Submodule K L) :
    Finset (ZMod (q ^ 2 + q + 1)) :=
  @Finset.filter _ (fun i => (g : L) ^ i.val ∈ W) (Classical.decPred _) Finset.univ

omit [Fintype K] in
/-- The elements of `L` lying in `W`, as a finset. -/
private noncomputable def sgC (W : Submodule K L) : Finset L :=
  @Finset.filter _ (fun y => y ∈ W) (Classical.decPred _) Finset.univ

omit [Fintype K] [Fintype L] in
/-- Membership in the trace unfolds. -/
private lemma sgTmem {q : ℕ} (g : Lˣ) (W : Submodule K L) :
    ∀ i : ZMod (q ^ 2 + q + 1), i ∈ sgT q g W ↔ (g : L) ^ i.val ∈ W := by
  intro i
  simp only [sgT, Finset.mem_filter, Finset.mem_univ, true_and]

omit [Fintype K] in
/-- Membership in the element finset unfolds. -/
private lemma sgCmem (W : Submodule K L) :
    ∀ y : L, y ∈ sgC W ↔ y ∈ W := by
  intro y
  simp only [sgC, Finset.mem_filter, Finset.mem_univ, true_and]


omit [Fintype L] in
/-- Injectivity core for the counting map: agreement of two values with ordered
exponents forces equality of indices and scalars. -/
private lemma sgPsiCore {q : ℕ} [Finite L]
    (hqK : Fintype.card K = q) (hfr : Module.finrank K L = 3)
    (g : Lˣ) (hg : ∀ x : Lˣ, x ∈ Subgroup.zpowers g)
    (i j : ZMod (q ^ 2 + q + 1)) (c d : Kˣ)
    (h : algebraMap K L (c : K) * (g : L) ^ i.val
      = algebraMap K L (d : K) * (g : L) ^ j.val)
    (hle : i.val ≤ j.val) : i = j ∧ c = d := by
  classical
  have : NeZero (q ^ 2 + q + 1) := ⟨by positivity⟩
  have halg_inj : Function.Injective (algebraMap K L) := RingHom.injective _
  have hg0 : (g : L) ≠ 0 := Units.ne_zero g
  have hX : (g : L) ^ i.val ≠ 0 := pow_ne_zero _ hg0
  have hB : algebraMap K L (d : K) ≠ 0 := by
    intro hz
    exact Units.ne_zero d (halg_inj (by rw [hz, map_zero]))
  have hsplit : j.val = i.val + (j.val - i.val) := (Nat.add_sub_cancel' hle).symm
  have hgj : (g : L) ^ j.val = (g : L) ^ i.val * (g : L) ^ (j.val - i.val) := by
    conv_lhs => rw [hsplit]
    rw [pow_add]
  have key : (g : L) ^ (j.val - i.val) * algebraMap K L (d : K)
      = algebraMap K L (c : K) := by
    have hX' : (g : L) ^ i.val * algebraMap K L (c : K)
        = (g : L) ^ i.val * ((g : L) ^ (j.val - i.val)
          * algebraMap K L (d : K)) := by
      rw [← mul_assoc, ← hgj]
      linear_combination h
    exact (mul_left_cancel₀ hX hX').symm
  have hY : (g : L) ^ (j.val - i.val)
      = algebraMap K L ((c : K) / (d : K)) := by
    rw [map_div₀, eq_div_iff hB]
    exact key
  have hmemN : (g : L) ^ (j.val - i.val) ∈ Set.range (algebraMap K L) :=
    ⟨_, hY.symm⟩
  have hdvd := (sgN4 hqK hfr g hg _).mp hmemN
  have hlt : j.val - i.val < q ^ 2 + q + 1 := by
    have hj := ZMod.val_lt j
    omega
  have hji : j.val - i.val = 0 := by
    rcases Nat.eq_zero_or_pos (j.val - i.val) with h0 | hpos
    · exact h0
    · exfalso
      have hleN := Nat.le_of_dvd hpos hdvd
      omega
  have hval : i.val = j.val := by omega
  have hij : i = j := ZMod.val_injective _ hval
  have h2 := h
  rw [← hval] at h2
  have hcdK : (c : K) = (d : K) := halg_inj (mul_right_cancel₀ hX h2)
  exact ⟨hij, Units.ext hcdK⟩

/-- The trace times `Kˣ`, plus zero, counts the elements of `W`. -/
private lemma sgN6count {q : ℕ} [DecidableEq K] [Finite L]
    (hqK : Fintype.card K = q) (hfr : Module.finrank K L = 3)
    (g : Lˣ) (hg : ∀ x : Lˣ, x ∈ Subgroup.zpowers g)
    (W : Submodule K L) :
    (sgT q g W).card * Fintype.card Kˣ + 1 = (sgC W).card := by
  classical
  have halg_inj : Function.Injective (algebraMap K L) := RingHom.injective _
  have hg0 : (g : L) ≠ 0 := Units.ne_zero g
  have hcA : ∀ c : Kˣ, algebraMap K L (c : K) ≠ 0 := by
    intro c hz
    exact Units.ne_zero c (halg_inj (by rw [hz, map_zero]))
  have hPsiinj : Function.Injective
      (fun p : ZMod (q ^ 2 + q + 1) × Kˣ =>
        algebraMap K L (p.2 : K) * (g : L) ^ p.1.val) := by
    intro ⟨i, c⟩ ⟨j, d⟩ h
    dsimp only at h
    rcases le_total i.val j.val with hle | hle
    · obtain ⟨hij, hcd⟩ := sgPsiCore hqK hfr g hg i j c d h hle
      exact Prod.ext hij hcd
    · obtain ⟨hji, hdc⟩ := sgPsiCore hqK hfr g hg j i d c h.symm hle
      exact Prod.ext hji.symm hdc.symm
  have himg : Finset.image
      (fun p : ZMod (q ^ 2 + q + 1) × Kˣ =>
        algebraMap K L (p.2 : K) * (g : L) ^ p.1.val)
      (sgT q g W ×ˢ Finset.univ) = (sgC W).erase 0 := by
    ext y
    rw [Finset.mem_image]
    constructor
    · rintro ⟨⟨i, c⟩, hprod, rfl⟩
      rw [Finset.mem_product] at hprod
      have hiT : i ∈ sgT q g W := hprod.1
      rw [sgTmem g W i] at hiT
      rw [Finset.mem_erase]
      refine ⟨?_, ?_⟩
      · change algebraMap K L (c : K) * (g : L) ^ i.val ≠ 0
        exact mul_ne_zero (hcA c) (pow_ne_zero _ hg0)
      · rw [sgCmem W _]
        change algebraMap K L (c : K) * (g : L) ^ i.val ∈ W
        rw [← Algebra.smul_def]
        exact W.smul_mem _ hiT
    · intro hy
      rw [Finset.mem_erase] at hy
      rw [sgCmem W y] at hy
      obtain ⟨hy0, hyW⟩ := hy
      obtain ⟨k, hk⟩ := sgN3 g hg y hy0
      have hyWk : (g : L) ^ k ∈ W := hk ▸ hyW
      have hmod : (k : ZMod (q ^ 2 + q + 1)).val = k % (q ^ 2 + q + 1) :=
        ZMod.val_natCast _ _
      have hTW : (k : ZMod (q ^ 2 + q + 1)) ∈ sgT q g W := by
        rw [sgTmem g W _, hmod]
        exact (sgN5 hqK hfr g hg W k).mp hyWk
      have hdvd : (q ^ 2 + q + 1) ∣ (q ^ 2 + q + 1) * (k / (q ^ 2 + q + 1)) :=
        dvd_mul_right _ _
      obtain ⟨cK, hcK⟩ := (sgN4 hqK hfr g hg _).mpr hdvd
      have hpow0 : (g : L) ^ ((q ^ 2 + q + 1) * (k / (q ^ 2 + q + 1))) ≠ 0 :=
        pow_ne_zero _ hg0
      have hcK0 : cK ≠ 0 := by
        intro hz
        rw [hz, map_zero] at hcK
        exact hpow0 hcK.symm
      refine ⟨⟨(k : ZMod (q ^ 2 + q + 1)), Units.mk0 cK hcK0⟩,
        Finset.mem_product.mpr ⟨hTW, Finset.mem_univ _⟩, ?_⟩
      change algebraMap K L ((Units.mk0 cK hcK0 : Kˣ) : K)
          * (g : L) ^ ((k : ZMod (q ^ 2 + q + 1)).val) = y
      rw [show ((Units.mk0 cK hcK0 : Kˣ) : K) = cK from rfl, hmod, hcK,
        ← pow_add, Nat.div_add_mod k (q ^ 2 + q + 1), hk]
  have hcard_img : (Finset.image
      (fun p : ZMod (q ^ 2 + q + 1) × Kˣ =>
        algebraMap K L (p.2 : K) * (g : L) ^ p.1.val)
      (sgT q g W ×ˢ Finset.univ)).card
      = (sgT q g W).card * Fintype.card Kˣ := by
    rw [Finset.card_image_of_injective _ hPsiinj, Finset.card_product,
      Finset.card_univ]
  have h0mem : (0 : L) ∈ sgC W := by
    rw [sgCmem W _]
    exact W.zero_mem
  have hfin : (sgT q g W).card * Fintype.card Kˣ = ((sgC W).erase 0).card := by
    rw [← hcard_img, himg]
  rw [Finset.card_erase_of_mem h0mem] at hfin
  have hCpos : 0 < (sgC W).card := Finset.card_pos.mpr ⟨0, h0mem⟩
  omega

/-- The element finset has `q ^ finrank` elements. -/
private lemma sgN6card {q : ℕ} [Finite L]
    (hqK : Fintype.card K = q) (W : Submodule K L) :
    (sgC W).card = q ^ Module.finrank K ↥W := by
  classical
  have h2 : (sgC W).card = Fintype.card ↥W := by
    unfold sgC
    rw [← Fintype.card_subtype]
  have h3 := Module.card_eq_pow_finrank (K := K) (V := ↥W)
  rw [hqK] at h3
  rw [h2, h3]

omit [Fintype L] in
/-- A 2-dimensional subspace and its trace of size `q + 1`. -/
private lemma sgN7 {q : ℕ} [Finite L]
    (hqK : Fintype.card K = q) (hfr : Module.finrank K L = 3)
    (g : Lˣ) (hg : ∀ x : Lˣ, x ∈ Subgroup.zpowers g) :
    ∃ H : Submodule K L, Module.finrank K ↥H = 2 ∧ (sgT q g H).card = q + 1 := by
  classical
  have : Fintype L := Fintype.ofFinite L
  let b := Module.finBasisOfFinrankEq K L hfr
  let f : Fin 2 → Fin 3 := fun i => ⟨i.val, by have h := i.isLt; omega⟩
  have hf : Function.Injective f := by
    intro a c hab
    have h2 : (f a).val = (f c).val := congrArg Fin.val hab
    exact Fin.ext h2
  have hli : LinearIndependent K (b ∘ f) := b.linearIndependent.comp f hf
  have hfr2 : Module.finrank K ↥(Submodule.span K (Set.range (b ∘ f))) = 2 := by
    rw [finrank_span_eq_card hli, Fintype.card_fin]
  refine ⟨Submodule.span K (Set.range (b ∘ f)), hfr2, ?_⟩
  set H : Submodule K L := Submodule.span K (Set.range (b ∘ f))
  have hcount := sgN6count hqK hfr g hg H
  have hcard := sgN6card hqK H
  have hK := sgN2_cardKu hqK
  have h2le := sgN2_two_le hqK
  rw [hfr2] at hcard
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  have hmK : Fintype.card Kˣ = m := by omega
  rw [hmK] at hcount
  have hexpand : (m + 1) ^ 2 = m * (m + 2) + 1 := by ring
  have key : (sgT (m + 1) g H).card * m = m * (m + 2) := by omega
  rw [mul_comm m (m + 2)] at key
  have hmpos : 0 < m := by omega
  have hTeq : (sgT (m + 1) g H).card = m + 2 :=
    Nat.eq_of_mul_eq_mul_right hmpos key
  omega

omit [Fintype L] in
/-- The translate of `H` by a nonzero exponent differs from `H`. -/
private lemma sgN8 {q : ℕ} [Finite L]
    (hqK : Fintype.card K = q) (hfr : Module.finrank K L = 3)
    (g : Lˣ) (hg : ∀ x : Lˣ, x ∈ Subgroup.zpowers g)
    (H : Submodule K L) (hHfr : Module.finrank K ↥H = 2)
    (x : ZMod (q ^ 2 + q + 1)) (hx : x ≠ 0) :
    H.comap (LinearMap.mulLeft K ((g : L) ^ x.val)) ≠ H := by
  classical
  have : Fintype L := Fintype.ofFinite L
  have : NeZero (q ^ 2 + q + 1) := ⟨by positivity⟩
  have h2le := sgN2_two_le hqK
  set u : L := (g : L) ^ x.val
  have hu0 : u ≠ 0 := pow_ne_zero _ (Units.ne_zero g)
  have hxval0 : x.val ≠ 0 := by
    intro hz
    exact hx ((ZMod.val_eq_zero x).mp hz)
  have hxlt : x.val < q ^ 2 + q + 1 := ZMod.val_lt x
  have huN : u ∉ Set.range (algebraMap K L) := by
    intro hmem
    have hdvd := (sgN4 hqK hfr g hg _).mp hmem
    have hleN := Nat.le_of_dvd (by omega : 0 < x.val) hdvd
    omega
  have hHbot : H ≠ ⊥ := by
    intro hbot
    rw [hbot] at hHfr
    rw [finrank_bot K L] at hHfr
    omega
  obtain ⟨y0, hy0W, hy00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hHbot
  set S : Subalgebra K L :=
    { carrier := {z | ∀ y ∈ H, z * y ∈ H}
      mul_mem' := by
        intro a c ha hc y hy
        rw [mul_assoc]
        exact ha _ (hc _ hy)
      add_mem' := by
        intro a c ha hc y hy
        rw [add_mul]
        exact H.add_mem (ha _ hy) (hc _ hy)
      one_mem' := by
        intro y hy
        rw [one_mul]
        exact hy
      zero_mem' := by
        intro y hy
        rw [zero_mul]
        exact H.zero_mem
      algebraMap_mem' := by
        intro c y hy
        rw [← Algebra.smul_def]
        exact H.smul_mem c hy }
  have hSmem : ∀ z : L, z ∈ S ↔ ∀ y ∈ H, z * y ∈ H := by
    intro z
    constructor
    · intro hz y hy
      exact hz y hy
    · intro h y hy
      exact h y hy
  intro hcon
  have huS : u ∈ S := by
    rw [hSmem]
    intro y hy
    have hyH' : y ∈ H.comap (LinearMap.mulLeft K u) := by
      rw [hcon]
      exact hy
    have hmem := Submodule.mem_comap.mp hyH'
    rwa [LinearMap.mulLeft_apply] at hmem
  have hSadj : Algebra.adjoin K {u} ≤ S := by
    apply Algebra.adjoin_le
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    exact huS
  have halg : IsAlgebraic K u := IsAlgebraic.of_finite K u
  have hident : (K⟮u⟯).toSubalgebra = Algebra.adjoin K {u} :=
    IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic halg
  have htower := Module.finrank_mul_finrank K ↥K⟮u⟯ L
  rw [hfr] at htower
  have hdvd3 : Module.finrank K ↥K⟮u⟯ ∣ 3 :=
    ⟨Module.finrank ↥K⟮u⟯ L, htower.symm⟩
  have hne1 : Module.finrank K ↥K⟮u⟯ ≠ 1 := by
    intro h1
    have hbot : K⟮u⟯ = ⊥ := (IntermediateField.finrank_eq_one_iff).mp h1
    have hself : u ∈ Algebra.adjoin K {u} :=
      Algebra.subset_adjoin (Set.mem_singleton u)
    rw [← hident] at hself
    rw [IntermediateField.mem_toSubalgebra] at hself
    rw [hbot] at hself
    rw [IntermediateField.mem_bot] at hself
    exact huN hself
  have hfr3 : Module.finrank K ↥K⟮u⟯ = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h1 | h3
    · exact absurd h1 hne1
    · exact h3
  have htop : K⟮u⟯ = ⊤ := by
    apply IntermediateField.eq_of_le_of_finrank_eq le_top
    rw [IntermediateField.finrank_top', hfr]
    exact hfr3
  have hStopTop : S.toSubmodule = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have hleSub : (Algebra.adjoin K {u}).toSubmodule ≤ S.toSubmodule :=
      fun z hz => hSadj hz
    have hmono := Submodule.finrank_mono hleSub
    have hadjfin : Module.finrank K ↥(Algebra.adjoin K {u}).toSubmodule = 3 := by
      rw [← hident, Subalgebra.finrank_toSubmodule]
      exact hfr3
    have hleS : Module.finrank K ↥S.toSubmodule ≤ Module.finrank K L :=
      Submodule.finrank_le _
    rw [hfr, ← hadjfin] at hleS ⊢
    omega
  have hall : ∀ z : L, z ∈ S := by
    intro z
    have hzT : z ∈ S.toSubmodule := by
      rw [hStopTop]
      exact Submodule.mem_top
    exact hzT
  have hallH : ∀ z : L, z ∈ H := by
    intro z
    have hzS := hall (z * y0⁻¹)
    rw [hSmem] at hzS
    have hmem := hzS y0 hy0W
    have heq : (z * y0⁻¹) * y0 = z := by
      rw [mul_assoc, inv_mul_cancel₀ hy00, mul_one]
    rw [heq] at hmem
    exact hmem
  have htopH : H = ⊤ := Submodule.eq_top_iff'.mpr hallH
  rw [htopH] at hHfr
  rw [finrank_top, hfr] at hHfr
  omega

omit [Fintype K] in
omit [Fintype L] in
/-- The translate has the same rank as `H`. -/
private lemma sgN9fin (H : Submodule K L) (u : L) (hu : u ≠ 0) :
    Module.finrank K ↥(H.comap (LinearMap.mulLeft K u))
      = Module.finrank K ↥H := by
  classical
  have e : ↥H ≃ₗ[K] ↥(H.comap (LinearMap.mulLeft K u)) :=
    { toFun := fun y =>
        ⟨u⁻¹ * (y : L), by
          rw [Submodule.mem_comap, LinearMap.mulLeft_apply,
            mul_inv_cancel_left₀ hu]
          exact y.2⟩
      map_add' := fun a b => by
        apply Subtype.ext
        change u⁻¹ * ((a : L) + (b : L)) = u⁻¹ * (a : L) + u⁻¹ * (b : L)
        rw [mul_add]
      map_smul' := fun c y => by
        apply Subtype.ext
        change u⁻¹ * (c • (y : L)) = c • (u⁻¹ * (y : L))
        rw [Algebra.smul_def, Algebra.smul_def, mul_left_comm]
      invFun := fun z =>
        ⟨u * (z : L), by
          have h := Submodule.mem_comap.mp z.2
          rwa [LinearMap.mulLeft_apply] at h⟩
      left_inv := fun z => by
        apply Subtype.ext
        change u * (u⁻¹ * ((z : L))) = (z : L)
        exact mul_inv_cancel_left₀ hu _
      right_inv := fun y => by
        apply Subtype.ext
        change u⁻¹ * (u * ((y : L))) = (y : L)
        exact inv_mul_cancel_left₀ hu _ }
  exact (LinearEquiv.finrank_eq e).symm

omit [Fintype L] in
/-- The intersection of `H` with its nonzero translate is a point. -/
private lemma sgN9 {q : ℕ} [Finite L]
    (hqK : Fintype.card K = q) (hfr : Module.finrank K L = 3)
    (g : Lˣ) (hg : ∀ x : Lˣ, x ∈ Subgroup.zpowers g)
    (H : Submodule K L) (hHfr : Module.finrank K ↥H = 2)
    (x : ZMod (q ^ 2 + q + 1)) (hx : x ≠ 0) :
    Module.finrank K ↥(H ⊓ H.comap (LinearMap.mulLeft K ((g : L) ^ x.val))) = 1 := by
  classical
  have hu0 : (g : L) ^ x.val ≠ 0 := pow_ne_zero _ (Units.ne_zero g)
  have hH'fr :
      Module.finrank K ↥(H.comap (LinearMap.mulLeft K ((g : L) ^ x.val))) = 2 := by
    rw [sgN9fin H _ hu0]
    exact hHfr
  have hsup :
      Module.finrank K ↥(H ⊔ H.comap (LinearMap.mulLeft K ((g : L) ^ x.val)))
        + Module.finrank K ↥(H ⊓ H.comap (LinearMap.mulLeft K ((g : L) ^ x.val)))
        = 4 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq H
      (H.comap (LinearMap.mulLeft K ((g : L) ^ x.val)))
    rw [hHfr, hH'fr] at h
    omega
  have hle :
      Module.finrank K ↥(H ⊔ H.comap (LinearMap.mulLeft K ((g : L) ^ x.val))) ≤ 3 := by
    have h := Submodule.finrank_le
      (H ⊔ H.comap (LinearMap.mulLeft K ((g : L) ^ x.val)))
    rw [hfr] at h
    exact h
  have hge :
      1 ≤ Module.finrank K ↥(H ⊓ H.comap (LinearMap.mulLeft K ((g : L) ^ x.val))) := by
    omega
  by_contra hne
  have h2 :
      2 ≤ Module.finrank K ↥(H ⊓ H.comap (LinearMap.mulLeft K ((g : L) ^ x.val))) := by
    omega
  have hWH : H ⊓ H.comap (LinearMap.mulLeft K ((g : L) ^ x.val)) = H :=
    Submodule.eq_of_le_of_finrank_le inf_le_left (by rw [hHfr]; exact h2)
  have hWH' : H ⊓ H.comap (LinearMap.mulLeft K ((g : L) ^ x.val))
      = H.comap (LinearMap.mulLeft K ((g : L) ^ x.val)) :=
    Submodule.eq_of_le_of_finrank_le inf_le_right (by rw [hH'fr]; exact h2)
  have hHeq : H.comap (LinearMap.mulLeft K ((g : L) ^ x.val)) = H :=
    hWH'.symm.trans hWH
  exact sgN8 hqK hfr g hg H hHfr x hx hHeq

omit [Fintype L] in
/-- Unique translate landing back in the trace. -/
private lemma sgN10 {q : ℕ} [Finite L]
    (hqK : Fintype.card K = q) (hfr : Module.finrank K L = 3)
    (g : Lˣ) (hg : ∀ x : Lˣ, x ∈ Subgroup.zpowers g)
    (H : Submodule K L) (hHfr : Module.finrank K ↥H = 2)
    (x : ZMod (q ^ 2 + q + 1)) (hx : x ≠ 0) :
    ∃! b : ZMod (q ^ 2 + q + 1), b ∈ sgT q g H ∧ b + x ∈ sgT q g H := by
  classical
  have : Fintype L := Fintype.ofFinite L
  have hchar : ∀ i : ZMod (q ^ 2 + q + 1),
      i ∈ sgT q g (H ⊓ H.comap (LinearMap.mulLeft K ((g : L) ^ x.val))) ↔
        (i ∈ sgT q g H ∧ i + x ∈ sgT q g H) := by
    intro i
    rw [sgTmem g _ i, Submodule.mem_inf, sgTmem g H i]
    constructor
    · rintro ⟨hiH, hiH'⟩
      refine ⟨hiH, ?_⟩
      rw [Submodule.mem_comap, LinearMap.mulLeft_apply] at hiH'
      have hpow : (g : L) ^ x.val * (g : L) ^ i.val = (g : L) ^ (x.val + i.val) :=
        (pow_add _ _ _).symm
      rw [hpow] at hiH'
      exact (sgTmem g H (i + x)).mpr ((sgN5cor hqK hfr g hg H i x).mpr hiH')
    · rintro ⟨hiH, hiHx⟩
      refine ⟨hiH, ?_⟩
      rw [Submodule.mem_comap, LinearMap.mulLeft_apply]
      have hmem := (sgTmem g H (i + x)).mp hiHx
      have hmem2 := (sgN5cor hqK hfr g hg H i x).mp hmem
      have hpow : (g : L) ^ (x.val + i.val)
          = (g : L) ^ x.val * (g : L) ^ i.val := pow_add _ _ _
      rw [hpow] at hmem2
      exact hmem2
  have hWfr :
      Module.finrank K ↥(H ⊓ H.comap (LinearMap.mulLeft K ((g : L) ^ x.val))) = 1 :=
    sgN9 hqK hfr g hg H hHfr x hx
  have hcount :=
    sgN6count hqK hfr g hg (H ⊓ H.comap (LinearMap.mulLeft K ((g : L) ^ x.val)))
  have hcard :=
    sgN6card hqK (H ⊓ H.comap (LinearMap.mulLeft K ((g : L) ^ x.val)))
  have hK := sgN2_cardKu hqK
  rw [hWfr, pow_one] at hcard
  have hm0 : Fintype.card Kˣ ≠ 0 := by
    have h2 := sgN2_two_le hqK
    omega
  have hT1 : (sgT q g (H ⊓ H.comap (LinearMap.mulLeft K ((g : L) ^ x.val)))).card
      = 1 := by
    have key : (sgT q g (H ⊓ H.comap (LinearMap.mulLeft K ((g : L) ^ x.val)))).card
        * Fintype.card Kˣ = 1 * Fintype.card Kˣ := by
      rw [one_mul]
      omega
    exact mul_right_cancel₀ hm0 key
  obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hT1
  have hmem : b ∈ sgT q g (H ⊓ H.comap (LinearMap.mulLeft K ((g : L) ^ x.val))) := by
    rw [hb]
    exact Finset.mem_singleton_self b
  obtain ⟨hbH, hbxH⟩ := (hchar b).mp hmem
  refine ⟨b, ⟨hbH, hbxH⟩, ?_⟩
  intro c hc
  have hcW : c ∈ sgT q g (H ⊓ H.comap (LinearMap.mulLeft K ((g : L) ^ x.val))) :=
    (hchar c).mpr hc
  rw [hb] at hcW
  exact Finset.mem_singleton.mp hcW

omit [Fintype L] in
/-- Core: the trace of a plane is the wanted difference set. -/
private theorem sgCore {q : ℕ} [Finite L]
    (hqK : Fintype.card K = q) (hfr : Module.finrank K L = 3) :
    ∃ D : Finset (ZMod (q ^ 2 + q + 1)), D.card = q + 1 ∧
      ∀ x : ZMod (q ^ 2 + q + 1), x ≠ 0 →
        ∃! ab : D × D, (ab.1 : ZMod (q ^ 2 + q + 1)) -
          (ab.2 : ZMod (q ^ 2 + q + 1)) = x := by
  classical
  have : Fintype L := Fintype.ofFinite L
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Lˣ)
  obtain ⟨H, hHfr, hHcard⟩ := sgN7 hqK hfr g hg
  refine ⟨sgT q g H, hHcard, ?_⟩
  intro x hx
  obtain ⟨b, hbmem, hbuniq⟩ := sgN10 hqK hfr g hg H hHfr x hx
  obtain ⟨hbH, hbxH⟩ := hbmem
  refine ⟨(⟨b + x, hbxH⟩, ⟨b, hbH⟩), ?_, ?_⟩
  · exact add_sub_cancel_left b x
  · intro ⟨a', b'⟩ hpair
    have ha'eq : (a' : ZMod (q ^ 2 + q + 1)) = (b' : ZMod (q ^ 2 + q + 1)) + x := by
      linear_combination hpair
    have hb'x : (b' : ZMod (q ^ 2 + q + 1)) + x ∈ sgT q g H := ha'eq ▸ a'.2
    have hb'eq : (b' : ZMod (q ^ 2 + q + 1)) = b := hbuniq _ ⟨b'.2, hb'x⟩
    have ha'x : (a' : ZMod (q ^ 2 + q + 1)) = b + x := by rw [ha'eq, hb'eq]
    exact Prod.ext (Subtype.ext ha'x) (Subtype.ext hb'eq)

end SingerPrivate

@[expose]
public section

/-- **Singer's difference set theorem.** For every prime power $q$, there is a subset $D$ of the
cyclic group $\mathbb{Z}/(q^2 + q + 1)\mathbb{Z}$ with $q + 1$ elements such that every nonzero
element $x$ of this group can be written as $x = a - b$ for exactly one ordered pair $(a, b)$ of
elements of $D$.

Proves `Wanted` entry `singer_cyclic_difference_set_exists`. -/
public theorem singer_cyclic_difference_set_exists
    (q : ℕ) (hq : IsPrimePow q) :
    ∃ D : Finset (ZMod (q ^ 2 + q + 1)), D.card = q + 1 ∧
      ∀ x : ZMod (q ^ 2 + q + 1), x ≠ 0 →
        ∃! ab : D × D, (ab.1 : ZMod (q ^ 2 + q + 1)) -
          (ab.2 : ZMod (q ^ 2 + q + 1)) = x := by
  obtain ⟨p, n, hp, hn, hpn⟩ := (isPrimePow_nat_iff q).mp hq
  subst hpn
  have : Fact p.Prime := ⟨hp⟩
  have hn0 : n ≠ 0 := ne_of_gt hn
  have h3n0 : 3 * n ≠ 0 := mul_ne_zero three_ne_zero hn0
  have hfrn : Module.finrank (ZMod p) (GaloisField p n) = n :=
    GaloisField.finrank (p := p) (n := n) hn0
  have hfr3n : Module.finrank (ZMod p) (GaloisField p (3 * n)) = 3 * n :=
    GaloisField.finrank (p := p) (n := 3 * n) h3n0
  obtain ⟨φ⟩ := FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod p)
    (K := GaloisField p n) (L := GaloisField p (3 * n)) (by
      rw [hfrn, hfr3n]
      exact dvd_mul_left n 3)
  let : Fintype (GaloisField p n) := Fintype.ofFinite _
  let : Fintype (GaloisField p (3 * n)) := Fintype.ofFinite _
  let : Algebra (GaloisField p n) (GaloisField p (3 * n)) :=
    RingHom.toAlgebra φ.toRingHom
  have hqK : Fintype.card (GaloisField p n) = p ^ n := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card (p := p) (n := n) hn0
  have hcardL : Fintype.card (GaloisField p (3 * n)) = p ^ (3 * n) := by
    rw [← Nat.card_eq_fintype_card]
    exact GaloisField.card (p := p) (n := 3 * n) h3n0
  have hfr : Module.finrank (GaloisField p n) (GaloisField p (3 * n)) = 3 := by
    have hL := Module.card_eq_pow_finrank (K := GaloisField p n)
      (V := GaloisField p (3 * n))
    rw [hqK, hcardL, ← pow_mul] at hL
    have hmul : 3 * n
        = n * Module.finrank (GaloisField p n) (GaloisField p (3 * n)) :=
      Nat.pow_right_injective hp.two_le hL
    have hmul2 : n * 3
        = n * Module.finrank (GaloisField p n) (GaloisField p (3 * n)) :=
      (mul_comm n 3).trans hmul
    exact (Nat.eq_of_mul_eq_mul_left hn hmul2).symm
  exact sgCore hqK hfr

end

end MetaMathlibExt
