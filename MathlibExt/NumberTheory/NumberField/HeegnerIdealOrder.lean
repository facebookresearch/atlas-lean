/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.SpecificGroups.Cyclic
public import Mathlib.RingTheory.FractionalIdeal.Basic
public import MathlibExt.NumberTheory.NumberField.Order

import Mathlib.RingTheory.DedekindDomain.Ideal.Basic
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.LinearCombination

/-!
# The ideal of index `N` in the order of conductor `n`

Let `K` be a number field with ring of integers `𝓞 K`, and let `n` be a natural number. The order
of conductor `n` is `𝒪_n = ℤ + n 𝓞 K` (`NumberField.orderOfConductor`); for `n ≠ 0` it is an order
of `K` in the sense of `NumberField.IsOrder` (`NumberField.isOrder_orderOfConductor`).

Let `𝒩` be an ideal of `𝓞 K` such that `𝓞 K ⧸ 𝒩` is cyclic of order `N`, as produced under the
Heegner hypothesis by
`NumberField.RingOfIntegers.exists_ideal_isAddCyclic_quotient_of_heegnerHypothesis`, and let
`𝒩_n = 𝒩 ∩ 𝒪_n` be its preimage in `𝒪_n`. Then `𝒪_n ⧸ 𝒩_n ≃+* ZMod N`
(`NumberField.orderOfConductor.nonempty_quotient_ringEquiv_zmod`, for any field `K`), and if
`N ≥ 1` and `n` is prime to `N` then `𝒩_n` is an invertible fractional ideal of `𝒪_n`
(`NumberField.orderOfConductor.nonempty_ringEquiv_zmod_and_isUnit`). This is the statement of
Gross, *Kolyvagin's work on modular elliptic curves*, 1991, §3, p. 238, for every number field `K`
rather than only imaginary quadratic fields.

## Proof

A ring whose additive group is cyclic is the image of `ℤ` (`IsAddCyclic.intCast_surjective`), so
`𝒪_n → 𝓞 K ⧸ 𝒩` is onto with kernel `𝒩_n`, and a cyclic ring of order `N` is `ZMod N`.

For invertibility, `N ∈ 𝒩_n` and `n 𝒩 ⊆ 𝒩_n`. For `z ∈ 𝒩⁻¹` (inverse in `𝓞 K`) the element
`n z` lies in the inverse of `𝒩_n` over `𝒪_n`, because `n z 𝒩 ⊆ n 𝓞 K ⊆ 𝒪_n`. Writing
`1 = s n + t N` and `1 = ∑ y_k z_k` with `y_k ∈ 𝒩`, `z_k ∈ 𝒩⁻¹`, each
`n y_k z_k = s (n y_k) (n z_k) + t N (n y_k z_k)` lies in `𝒩_n 𝒩_n⁻¹`; hence `n` does, so does
`N`, and therefore `1 = s n + t N` does.
-/

@[expose] public section

open NumberField nonZeroDivisors

/-- **A ring with cyclic additive group is a quotient of `ℤ`.** If the additive group of a ring
`R` is cyclic, then the canonical map `ℤ → R` is surjective. -/
theorem IsAddCyclic.intCast_surjective (R : Type*) [Ring R] [IsAddCyclic R] :
    Function.Surjective (Int.cast : ℤ → R) := by
  obtain ⟨g, hg⟩ := IsAddCyclic.exists_generator (α := R)
  obtain ⟨a, ha⟩ := hg 1
  obtain ⟨b, hb⟩ := hg (g * g)
  simp only at ha hb
  have hgb : ((b : ℤ) : R) = g := by
    calc ((b : ℤ) : R) = b • (1 : R) := (zsmul_one b).symm
      _ = b • (a • g) := by rw [ha]
      _ = a • (b • g) := smul_comm b a g
      _ = a • (g * g) := by rw [hb]
      _ = (a • g) * g := (smul_mul_assoc a g g).symm
      _ = g := by rw [ha, one_mul]
  intro x
  obtain ⟨m, rfl⟩ := hg x
  exact ⟨m * b, by simp only; push_cast; rw [hgb, zsmul_eq_mul]⟩

-- A ring with cyclic additive group is `ZMod` of its cardinality.
private theorem nonempty_ringEquiv_zmod_natCard (R : Type*) [Ring R] [IsAddCyclic R] :
    Nonempty (R ≃+* ZMod (Nat.card R)) := by
  have hsurj : Function.Surjective (ZMod.castHom (dvd_refl (ringChar R)) R) := fun r => by
    obtain ⟨m, rfl⟩ := IsAddCyclic.intCast_surjective R r
    exact ⟨m, map_intCast _ m⟩
  let e := RingEquiv.ofBijective _ ⟨ZMod.castHom_injective R, hsurj⟩
  have : Nat.card R = ringChar R := (Nat.card_congr e.toEquiv).symm.trans (Nat.card_zmod _)
  rw [this]
  exact ⟨e.symm⟩

-- The preimage of an ideal with cyclic quotient of order `N` has quotient `ZMod N`.
private theorem nonempty_quotient_comap_ringEquiv_zmod {S R : Type*} [CommRing S] [CommRing R]
    (φ : S →+* R) {I : Ideal R} (hcyc : IsAddCyclic (R ⧸ I)) {N : ℕ}
    (hcard : Nat.card (R ⧸ I) = N) : Nonempty (S ⧸ I.comap φ ≃+* ZMod N) := by
  subst hcard
  obtain ⟨e⟩ := nonempty_ringEquiv_zmod_natCard (R ⧸ I)
  have hsurj : Function.Surjective ((Ideal.Quotient.mk I).comp φ) := fun q => by
    obtain ⟨m, rfl⟩ := IsAddCyclic.intCast_surjective (R ⧸ I) q
    exact ⟨m, map_intCast _ m⟩
  have hker : I.comap φ = RingHom.ker ((Ideal.Quotient.mk I).comp φ) := by
    rw [← RingHom.comap_ker, Ideal.mk_ker]
  exact ⟨((Ideal.quotEquivOfEq hker).trans (RingHom.quotientKerEquivOfSurjective hsurj)).trans e⟩

namespace NumberField

variable (K : Type*) [Field K]

/-- **The order of conductor `n`.** For a field `K` and a natural number `n`, the `ℤ`-subalgebra
`ℤ + n 𝓞 K` of `K`, consisting of the elements `a + n y` with `a ∈ ℤ` and `y` in the ring of
integers `𝓞 K = integralClosure ℤ K`. When `K` is a number field and `n ≠ 0` it is an order of `K`
(`NumberField.isOrder_orderOfConductor`); for `n = 1` it is `𝓞 K`
(`NumberField.orderOfConductor_one`). -/
def orderOfConductor (n : ℕ) : Subalgebra ℤ K where
  carrier := {x | ∃ a : ℤ, ∃ y ∈ integralClosure ℤ K, x = a + n * y}
  mul_mem' := by
    rintro _ _ ⟨a, y, hy, rfl⟩ ⟨b, z, hz, rfl⟩
    refine ⟨a * b, a * z + b * y + n * (y * z), ?_, by push_cast; ring⟩
    have := (integralClosure ℤ K).intCast_mem a
    have := (integralClosure ℤ K).intCast_mem b
    have := (integralClosure ℤ K).natCast_mem n
    exact add_mem (add_mem (mul_mem ‹_› hz) (mul_mem ‹_› hy)) (mul_mem ‹_› (mul_mem hy hz))
  add_mem' := by
    rintro _ _ ⟨a, y, hy, rfl⟩ ⟨b, z, hz, rfl⟩
    exact ⟨a + b, y + z, add_mem hy hz, by push_cast; ring⟩
  algebraMap_mem' r := ⟨r, 0, zero_mem _, by simp⟩

variable {K}

theorem mem_orderOfConductor {n : ℕ} {x : K} :
    x ∈ orderOfConductor K n ↔ ∃ a : ℤ, ∃ y ∈ integralClosure ℤ K, x = a + n * y :=
  Iff.rfl

theorem natCast_mul_mem_orderOfConductor (n : ℕ) {y : K} (hy : y ∈ integralClosure ℤ K) :
    (n : K) * y ∈ orderOfConductor K n :=
  ⟨0, y, hy, by simp⟩

variable (K)

theorem orderOfConductor_le_integralClosure (n : ℕ) :
    orderOfConductor K n ≤ integralClosure ℤ K := by
  rintro _ ⟨a, y, hy, rfl⟩
  exact add_mem ((integralClosure ℤ K).intCast_mem a)
    (mul_mem ((integralClosure ℤ K).natCast_mem n) hy)

theorem orderOfConductor_one : orderOfConductor K 1 = integralClosure ℤ K := by
  refine le_antisymm (orderOfConductor_le_integralClosure K 1) fun y hy => ?_
  exact ⟨0, y, hy, by simp⟩

/-- The inclusion `ℤ + n 𝓞 K → 𝓞 K` of the order of conductor `n` into the ring of integers, as a
ring homomorphism. -/
def orderOfConductor.toRingOfIntegers (n : ℕ) : orderOfConductor K n →+* 𝓞 K where
  toFun x := ⟨x, orderOfConductor_le_integralClosure K n x.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

variable {K}

/-- **The quotient of the order of conductor `n` by `𝒩 ∩ 𝒪_n`.** Let `K` be a field, `n` a natural
number and `𝒩` an ideal of `𝓞 K` such that `𝓞 K ⧸ 𝒩` is cyclic of order `N`. Then the preimage
`𝒩_n` of `𝒩` in the order of conductor `n` satisfies `𝒪_n ⧸ 𝒩_n ≃+* ZMod N`. No hypothesis on
`n` or `N` is needed. -/
theorem orderOfConductor.nonempty_quotient_ringEquiv_zmod (n : ℕ) {𝒩 : Ideal (𝓞 K)} {N : ℕ}
    (hcyc : IsAddCyclic (𝓞 K ⧸ 𝒩)) (hcard : Nat.card (𝓞 K ⧸ 𝒩) = N) :
    Nonempty (orderOfConductor K n ⧸ 𝒩.comap (orderOfConductor.toRingOfIntegers K n) ≃+*
      ZMod N) :=
  nonempty_quotient_comap_ringEquiv_zmod _ hcyc hcard

variable [NumberField K]

variable (K) in
theorem isOrder_orderOfConductor {n : ℕ} (hn : n ≠ 0) :
    NumberField.IsOrder K (orderOfConductor K n) := by
  refine ⟨orderOfConductor_le_integralClosure K n, IsFractionRing.of_field _ K fun z => ?_⟩
  have := integralClosure.isFractionRing_of_finite_extension (A := ℤ) ℚ K
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := integralClosure ℤ K) z
  refine ⟨⟨_, natCast_mul_mem_orderOfConductor n a.2⟩,
    ⟨_, natCast_mul_mem_orderOfConductor n b.2⟩, ?_⟩
  have : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn
  change (a : K) / b = ((n : K) * a) / (n * b)
  rw [mul_div_mul_left _ _ this]

theorem orderOfConductor.isUnit_coeIdeal_comap {n N : ℕ} {𝒩 : Ideal (𝓞 K)}
    (hcard : Nat.card (𝓞 K ⧸ 𝒩) = N) (hN : 1 ≤ N) (hcop : n.Coprime N) :
    IsUnit ((𝒩.comap (orderOfConductor.toRingOfIntegers K n) : Ideal (orderOfConductor K n)) :
      FractionalIdeal (orderOfConductor K n)⁰ K) := by
  have hNmem : (N : 𝓞 K) ∈ 𝒩 := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, ← hcard, ← nsmul_one]
    exact card_nsmul_eq_zero'
  rcases eq_or_ne n 0 with rfl | hn
  · obtain rfl : N = 1 := Nat.coprime_zero_left _ |>.mp hcop
    obtain rfl : 𝒩 = ⊤ :=
      Ideal.Quotient.subsingleton_iff.mp (Nat.card_eq_one_iff_unique.mp hcard).1
    rw [Ideal.comap_top, FractionalIdeal.coeIdeal_top]
    exact isUnit_one
  have := (isOrder_orderOfConductor K hn).isFractionRing
  set O := orderOfConductor K n
  set ι := orderOfConductor.toRingOfIntegers K n
  set I := 𝒩.comap ι
  have hNI : (N : O) ∈ I := by rw [Ideal.mem_comap, map_natCast]; exact hNmem
  have hI0 : (I : FractionalIdeal O⁰ K) ≠ 0 := by
    refine FractionalIdeal.coeIdeal_eq_zero.not.mpr fun h => ?_
    rw [h, Ideal.mem_bot] at hNI
    have := congrArg (algebraMap O K) hNI
    simp only [map_natCast, map_zero, Nat.cast_eq_zero] at this
    omega
  have h𝒩0 : (𝒩 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 := by
    refine FractionalIdeal.coeIdeal_eq_zero.not.mpr fun h => ?_
    rw [h, Ideal.mem_bot] at hNmem
    have := congrArg (algebraMap (𝓞 K) K) hNmem
    simp only [map_natCast, map_zero, Nat.cast_eq_zero] at this
    omega
  -- elements of `O` lie in the inverse of `I`
  have hOinv : ∀ x ∈ O, x ∈ (I : FractionalIdeal O⁰ K)⁻¹ := fun x hx => by
    rw [FractionalIdeal.mem_inv_iff hI0]
    intro y hy
    obtain ⟨y', -, rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy
    exact (FractionalIdeal.mem_one_iff _).mpr ⟨⟨x, hx⟩ * y', by rw [map_mul]; rfl⟩
  -- `z y` is integral for `y ∈ 𝒩` and `z ∈ 𝒩⁻¹`
  have hint : ∀ y ∈ 𝒩, ∀ z ∈ (𝒩 : FractionalIdeal (𝓞 K)⁰ K)⁻¹,
      ∃ w : 𝓞 K, algebraMap (𝓞 K) K w = z * algebraMap (𝓞 K) K y := fun y hy z hz =>
    (FractionalIdeal.mem_one_iff _).mp ((FractionalIdeal.mem_inv_iff h𝒩0).mp hz _
      ((FractionalIdeal.mem_coeIdeal _).mpr ⟨y, hy, rfl⟩))
  -- `n y ∈ I` for `y ∈ 𝒩`
  have hny : ∀ y ∈ 𝒩, (n : K) * algebraMap (𝓞 K) K y ∈ (I : FractionalIdeal O⁰ K) := by
    intro y hy
    refine (FractionalIdeal.mem_coeIdeal _).mpr
      ⟨⟨_, natCast_mul_mem_orderOfConductor n y.2⟩, ?_, rfl⟩
    rw [Ideal.mem_comap]
    have : ι ⟨_, natCast_mul_mem_orderOfConductor n y.2⟩ = (n : 𝓞 K) * y := rfl
    rw [this]
    exact Ideal.mul_mem_left _ _ hy
  -- `n z ∈ I⁻¹` for `z ∈ 𝒩⁻¹`
  have hnz : ∀ z ∈ (𝒩 : FractionalIdeal (𝓞 K)⁰ K)⁻¹,
      (n : K) * z ∈ (I : FractionalIdeal O⁰ K)⁻¹ := by
    intro z hz
    rw [FractionalIdeal.mem_inv_iff hI0]
    intro i hi
    obtain ⟨i', hi', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hi
    obtain ⟨w, hw⟩ := hint (ι i') hi' z hz
    refine (FractionalIdeal.mem_one_iff _).mpr
      ⟨⟨_, natCast_mul_mem_orderOfConductor n w.2⟩, ?_⟩
    change (n : K) * algebraMap (𝓞 K) K w = n * z * algebraMap (𝓞 K) K (ι i')
    rw [hw, mul_assoc]
  set S := (I : FractionalIdeal O⁰ K) * (I : FractionalIdeal O⁰ K)⁻¹
  have hadd : ∀ x y, x ∈ S → y ∈ S → x + y ∈ S := fun x y hx hy =>
    Submodule.add_mem (S : Submodule O K) hx hy
  have hzsmul : ∀ (m : ℤ) x, x ∈ S → (m : K) * x ∈ S := fun m x hx => by
    rw [← zsmul_eq_mul]
    exact zsmul_mem (show x ∈ (S : Submodule O K) from hx) m
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop
  have hK : (u : K) * n + v * N = 1 := by exact_mod_cast huv
  have hNS : (N : K) ∈ S := by
    have := FractionalIdeal.mul_mem_mul
      ((FractionalIdeal.mem_coeIdeal _).mpr ⟨_, hNI, map_natCast _ _⟩) (hOinv 1 (one_mem _))
    rwa [mul_one] at this
  have hnS : (n : K) ∈ S := by
    have h1 : (1 : K) ∈ ((𝒩 : FractionalIdeal (𝓞 K)⁰ K) * (𝒩 : FractionalIdeal (𝓞 K)⁰ K)⁻¹) := by
      rw [mul_inv_cancel₀ h𝒩0]
      exact FractionalIdeal.one_mem_one _
    rw [← FractionalIdeal.mem_coeToSubmodule, FractionalIdeal.coeToSubmodule_mul] at h1
    rw [← mul_one (n : K)]
    refine Submodule.mul_induction_on h1 (fun y hy z hz => ?_) fun x y hx hy => ?_
    · obtain ⟨y', hy', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).mp hy
      obtain ⟨w, hw⟩ := hint y' hy' z hz
      have e : (n : K) * (algebraMap (𝓞 K) K y' * z) =
          u * ((n * algebraMap (𝓞 K) K y') * (n * z)) +
            v * (N * (n * algebraMap (𝓞 K) K w)) := by
        rw [hw]
        linear_combination (-(n : K) * algebraMap (𝓞 K) K y' * z) * hK
      rw [e]
      refine hadd _ _ (hzsmul u _ (FractionalIdeal.mul_mem_mul (hny y' hy') (hnz z hz)))
        (hzsmul v _ (FractionalIdeal.mul_mem_mul
          ((FractionalIdeal.mem_coeIdeal _).mpr ⟨_, hNI, map_natCast _ _⟩)
          (hOinv _ (natCast_mul_mem_orderOfConductor n w.2))))
    · rw [mul_add]
      exact hadd _ _ hx hy
  have h1S : (1 : K) ∈ S := by
    rw [← hK]
    exact hadd _ _ (hzsmul u _ hnS) (hzsmul v _ hNS)
  rw [← FractionalIdeal.mul_inv_cancel_iff_isUnit K]
  refine le_antisymm ?_ (FractionalIdeal.one_le.mpr h1S)
  refine FractionalIdeal.mul_le.mpr fun i hi j hj => ?_
  rw [mul_comm]
  exact (FractionalIdeal.mem_inv_iff hI0).mp hj i hi

/-- **The ideal of index `N` in the order of conductor `n`.** Let `K` be a number field, `N ≥ 1`
and `𝒩` an ideal of `𝓞 K` such that `𝓞 K ⧸ 𝒩` is cyclic of order `N`. Let `n` be a natural number
prime to `N`, let `𝒪_n = ℤ + n 𝓞 K` be the order of conductor `n` and let `𝒩_n = 𝒩 ∩ 𝒪_n` be the
preimage of `𝒩` in `𝒪_n`. Then `𝒪_n ⧸ 𝒩_n ≃+* ZMod N`, and `𝒩_n` is invertible: it is a unit in
the monoid of fractional ideals of `𝒪_n` in `K`.

The source states this for an imaginary quadratic field `K` and `n ≥ 1`; neither hypothesis is
used here (for `n = 0` coprimality forces `N = 1`, so `𝒩_n = 𝒪_n`). Neither `N ≥ 1` nor
coprimality is needed for the quotient (`orderOfConductor.nonempty_quotient_ringEquiv_zmod`).

Source: B. H. Gross, *Kolyvagin's work on modular elliptic curves*, in *L-functions and
arithmetic* (Durham, 1989), London Math. Soc. Lecture Note Ser. 153, Cambridge Univ. Press, 1991,
235–256, §3, p. 238 ("The ideal $\mathcal{N}_n = \mathcal{N} \cap \mathcal{O}_n$ is an invertible
$\mathcal{O}_n$-module with $\mathcal{O}_n/\mathcal{N}_n \simeq \mathbb{Z}/N\mathbb{Z}$"). -/
theorem orderOfConductor.nonempty_ringEquiv_zmod_and_isUnit {n N : ℕ} {𝒩 : Ideal (𝓞 K)}
    (hcyc : IsAddCyclic (𝓞 K ⧸ 𝒩)) (hcard : Nat.card (𝓞 K ⧸ 𝒩) = N) (hN : 1 ≤ N)
    (hcop : n.Coprime N) :
    Nonempty (orderOfConductor K n ⧸ 𝒩.comap (orderOfConductor.toRingOfIntegers K n) ≃+*
      ZMod N) ∧
    IsUnit ((𝒩.comap (orderOfConductor.toRingOfIntegers K n) : Ideal (orderOfConductor K n)) :
      FractionalIdeal (orderOfConductor K n)⁰ K) :=
  ⟨nonempty_quotient_ringEquiv_zmod n hcyc hcard, isUnit_coeIdeal_comap hcard hN hcop⟩

end NumberField

end
