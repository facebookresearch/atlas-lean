/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-
Modifications (c) 2026 Meta Platforms, Inc. and affiliates:
ported from `TauCeti/RingTheory/Invariant/Localization.lean` in TauCetiProject/TauCeti at
revision 62bbc0596dc3539d488232e4e924a338548ea0a9. Preserve the complete localization and
stalk-injectivity proofs in a standalone MathlibExt module. No unresolved result is added.
-/
module


public import Mathlib.Algebra.Algebra.Subalgebra.Operations
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Basic
import Mathlib.RingTheory.Ideal.Operations

/-!
# Invariant rings and localization

Let a group `G` act on a commutative ring `A` by ring automorphisms, and write `Aᴳ` for the
invariant subring `FixedPoints.subring A G`. This file compares invariants with localization.

For a submonoid `M` of invariant elements, the action extends to the localization `M⁻¹A`
(`Localization (Algebra.algebraMapSubmonoid A M)`), compatibly with `A → M⁻¹A`. When `G` is
finite, taking invariants commutes with this localization: `(M⁻¹A)ᴳ` is the localization of `Aᴳ`
at `M`. A fraction `a / s` fixed by every `g` satisfies `t_g (g • a - a) = 0` for some `t_g ∈ M`,
which can be replaced by the product `t` of the `t_g` because `G` is finite, and then
`a / s = t a / (s t)` with `t a` invariant. Taking `M` to be the powers of an invariant `r` gives
the localization `A[1/r]` of `A` at `r`. The argument only uses finitely many ring endomorphisms
compatible with the localization map, and is stated in that form for an arbitrary localization
`S` of `A`, whose fixed elements are described by an arbitrary ring `R'` mapping injectively to
`S` (`TauCeti.FixedPoints.isLocalization_of_mem_range_iff`).

Also for finite `G`, the local homomorphism `(Aᴳ)_P → A_Q` induced by `Aᴳ ⊆ A` at a prime `Q` of
`A` lying over a prime `P` of `Aᴳ` is injective. If an invariant `a` is killed by some `t ∉ Q`,
prime avoidance applied to the annihilator of `a`, which is `G`-stable, and the finitely many
primes `g⁻¹ • Q` gives such a `t` outside every `g⁻¹ • Q`; then the invariant `∏ g, g • t` lies
outside `P` and kills `a`.

These are the two local facts behind the categorical universal property of the affine invariant
quotient `Spec A ⟶ Spec Aᴳ` for arbitrary target schemes.

## Main definitions

* `TauCeti.FixedPoints.localizationRingAut M`: the action of `G` on `M⁻¹A` for a submonoid `M`
  of invariants, which provides the instance
  `MulSemiringAction G (Localization (Algebra.algebraMapSubmonoid A M))`.
* The instance `Algebra (FixedPoints.subring A G)
  (FixedPoints.subring (Localization (Algebra.algebraMapSubmonoid A M)) G)` given by `A → M⁻¹A`.

## Main results

* `TauCeti.FixedPoints.smul_algebraMap_localization`: `A → M⁻¹A` is `G`-equivariant.
* `TauCeti.FixedPoints.smul_mk'`: `G` acts on a fraction `a / s` through its numerator.
* `TauCeti.FixedPoints.isLocalization_of_mem_range_iff`: the elements of a localization fixed by
  finitely many compatible ring endomorphisms are the localization of the fixed elements.
* `TauCeti.FixedPoints.isLocalization`: for finite `G`, `(M⁻¹A)ᴳ` is the localization of `Aᴳ`
  at `M`.
* `Ideal.exists_mem_forall_smul_notMem`: for finite `G`, prime avoidance for the translates
  `g⁻¹ • Q` of a prime `Q`.
* `Ideal.exists_notMem_dvd_of_forall_smul_notMem`: for finite `G`, an element outside every
  `g⁻¹ • Q` divides an invariant outside `Q`.
* `TauCeti.FixedPoints.localRingHom_injective`: for finite `G`, `(Aᴳ)_P → A_Q` is injective.

## References

* M. Demazure and A. Grothendieck, *Schémas en groupes (SGA 3)*, Exposé V, §1.
-/

public section

namespace TauCeti.FixedPoints

/-- **Fixed elements commute with localization.** Let `S` be a localization of `A` at the image of
a submonoid `M` of `R`, and let finitely many ring endomorphisms `σ i` of `A` and `τ i` of `S` be
compatible with `A → S`. If `R → A` and `R' → S` are injective with images the elements fixed by
every `σ i`, respectively every `τ i`, and `R → R'` is compatible with them, then `R'` is the
localization of `R` at `M`. A fraction `a / s` fixed by every `τ i` satisfies
`t_i (σ i a - a) = 0` for some `t_i ∈ M`, which can be replaced by the product `t` of the `t_i`
since there are finitely many `i`; then `a / s = t a / (s t)` with `t a` fixed. -/
theorem isLocalization_of_mem_range_iff {ι R A R' S : Type*} [Finite ι] [CommRing R]
    [CommRing A] [CommRing R'] [CommRing S] [Algebra R A] [Algebra A S] [Algebra R' S]
    [Algebra R R'] (M : Submonoid R) [IsLocalization (Algebra.algebraMapSubmonoid A M) S]
    (σ : ι → A →+* A) (τ : ι → S →+* S)
    (hστ : ∀ i a, τ i (algebraMap A S a) = algebraMap A S (σ i a))
    (hR : Function.Injective (algebraMap R A))
    (hσ : ∀ a, a ∈ Set.range (algebraMap R A) ↔ ∀ i, σ i a = a)
    (hR' : Function.Injective (algebraMap R' S))
    (hτ : ∀ s, s ∈ Set.range (algebraMap R' S) ↔ ∀ i, τ i s = s)
    (h : ∀ x, algebraMap R' S (algebraMap R R' x) = algebraMap A S (algebraMap R A x)) :
    IsLocalization M R' := by
  have hfix (x : R) (i : ι) :
      τ i (algebraMap A S (algebraMap R A x)) = algebraMap A S (algebraMap R A x) := by
    rw [hστ, (hσ _).mp ⟨x, rfl⟩ i]
  refine (_root_.isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
  · -- The image of `m ∈ M` is a unit of `S` whose inverse is again fixed.
    intro m
    have hu : IsUnit (algebraMap A S (algebraMap R A m)) :=
      IsLocalization.map_units S ⟨_, Algebra.mem_algebraMapSubmonoid_of_mem m⟩
    obtain ⟨v, hv⟩ := (hτ (hu.unit⁻¹ : Sˣ)).mpr fun i ↦ by
      refine Units.eq_inv_of_mul_eq_one_right ?_
      rw [← map_one (τ i), ← Units.inv_mul hu.unit, map_mul, IsUnit.unit_spec, hfix]
    refine isUnit_iff_exists_inv.mpr ⟨v, hR' ?_⟩
    rw [map_mul, h, hv, map_one]
    exact hu.mul_val_inv
  · -- A fixed fraction `a / s` equals `t a / (s t)` with `t ∈ M` and `t a` fixed.
    intro z
    obtain ⟨⟨a, _, ⟨s, hs, rfl⟩⟩, ha⟩ :=
      IsLocalization.surj (Algebra.algebraMapSubmonoid A M) (algebraMap R' S z)
    have hk (i : ι) : ∃ t ∈ M, algebraMap R A t * σ i a = algebraMap R A t * a := by
      have hi := congrArg (τ i) ha
      rw [map_mul, (hτ _).mp ⟨z, rfl⟩ i, hfix, hστ] at hi
      obtain ⟨⟨_, t, ht, rfl⟩, hti⟩ :=
        IsLocalization.exists_of_eq (M := Algebra.algebraMapSubmonoid A M) (hi.symm.trans ha)
      exact ⟨t, ht, hti⟩
    choose t ht hti using hk
    have := Fintype.ofFinite ι
    set T := ∏ i, t i
    have hT (i : ι) : algebraMap R A T * σ i a = algebraMap R A T * a := by
      obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem t (Finset.mem_univ i)
      rw [show T = t i * c from hc, map_mul, mul_comm (algebraMap R A (t i)), mul_assoc,
        mul_assoc, hti i]
    obtain ⟨b, hb⟩ := (hσ (algebraMap R A T * a)).mpr fun i ↦ by
      rw [map_mul, (hσ _).mp ⟨T, rfl⟩ i, hT i]
    refine ⟨(b, ⟨s * T, mul_mem hs (prod_mem fun i _ ↦ ht i)⟩), hR' ?_⟩
    simp only [map_mul, h, hb, ← ha]
    ring
  · -- Elements of `R` identified in `R'` are identified after multiplication by some `t ∈ M`.
    intro x y hxy
    have hxy' : algebraMap A S (algebraMap R A x) = algebraMap A S (algebraMap R A y) := by
      rw [← h, ← h, hxy]
    obtain ⟨⟨_, t, ht, rfl⟩, hty⟩ :=
      IsLocalization.exists_of_eq (M := Algebra.algebraMapSubmonoid A M) hxy'
    exact ⟨⟨t, ht⟩, hR (by simpa only [map_mul] using hty)⟩

variable {A G : Type*} [CommRing A] [Group G] [MulSemiringAction G A]

section Localization

variable (M : Submonoid (FixedPoints.subring A G))

/-- An element of `G` maps the image in `A` of a submonoid of invariants to itself. -/
private theorem map_algebraMapSubmonoid_toRingEquiv (g : G) :
    (Algebra.algebraMapSubmonoid A M).map (MulSemiringAction.toRingEquiv G A g).toMonoidHom =
      Algebra.algebraMapSubmonoid A M := by
  ext x
  simp only [Algebra.algebraMapSubmonoid, Submonoid.mem_map]
  constructor
  · rintro ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    exact ⟨m, hm, (m.2 g).symm⟩
  · rintro ⟨m, hm, rfl⟩
    exact ⟨_, ⟨m, hm, rfl⟩, m.2 g⟩

/-- The action of `G` on the localization `M⁻¹A` at a submonoid `M` of invariants, induced by its
action on `A`. -/
noncomputable def localizationRingAut :
    G →* RingAut (Localization (Algebra.algebraMapSubmonoid A M)) where
  toFun g := IsLocalization.ringEquivOfRingEquiv _ _ (MulSemiringAction.toRingEquiv G A g)
    (map_algebraMapSubmonoid_toRingEquiv M g)
  map_one' := RingEquiv.toRingHom_injective <|
    IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid A M) <| RingHom.ext fun a ↦ by simp
  map_mul' g h := RingEquiv.toRingHom_injective <|
    IsLocalization.ringHom_ext (Algebra.algebraMapSubmonoid A M) <| RingHom.ext fun a ↦ by
      simp

/-- The action of `G` on `M⁻¹A` given by `localizationRingAut`. -/
noncomputable instance instMulSemiringActionLocalization :
    MulSemiringAction G (Localization (Algebra.algebraMapSubmonoid A M)) :=
  MulSemiringAction.compHom _ (localizationRingAut M)

/-- `localizationRingAut M g` is the action of `g` on `M⁻¹A`. -/
theorem localizationRingAut_apply (g : G) (x : Localization (Algebra.algebraMapSubmonoid A M)) :
    localizationRingAut M g x = g • x :=
  rfl

/-- The action of `G` on `M⁻¹A` extends the action on `A`. -/
@[simp]
theorem smul_algebraMap_localization (g : G) (a : A) :
    g • algebraMap A (Localization (Algebra.algebraMapSubmonoid A M)) a =
      algebraMap A (Localization (Algebra.algebraMapSubmonoid A M)) (g • a) :=
  IsLocalization.ringEquivOfRingEquiv_eq (map_algebraMapSubmonoid_toRingEquiv M g) a

/-- The action of `G` on `M⁻¹A` on fractions: `g • (a / s) = (g • a) / s`, since the
denominator `s` is invariant. -/
@[simp]
theorem smul_mk' (g : G) (a : A) (s : Algebra.algebraMapSubmonoid A M) :
    g • IsLocalization.mk' (Localization (Algebra.algebraMapSubmonoid A M)) a s =
      IsLocalization.mk' _ (g • a) s := by
  obtain ⟨m, -, hm⟩ := s.2
  have hs : g • (s : A) = s := hm ▸ m.2 g
  rw [IsLocalization.eq_mk'_iff_mul_eq, ← hs, ← smul_algebraMap_localization,
    ← smul_algebraMap_localization, ← smul_mul', IsLocalization.mk'_spec]

/-- The localization map `A → M⁻¹A` sends invariants to invariants. -/
theorem algebraMap_mem_fixedPoints (a : FixedPoints.subring A G) :
    algebraMap A (Localization (Algebra.algebraMapSubmonoid A M)) a ∈
      FixedPoints.subring (Localization (Algebra.algebraMapSubmonoid A M)) G := fun g ↦ by
  rw [smul_algebraMap_localization, a.2 g]

/-- The algebra structure of `(M⁻¹A)ᴳ` over `Aᴳ` given by the localization map `A → M⁻¹A`. -/
noncomputable instance instAlgebraLocalization :
    Algebra (FixedPoints.subring A G)
      (FixedPoints.subring (Localization (Algebra.algebraMapSubmonoid A M)) G) :=
  (((algebraMap A (Localization (Algebra.algebraMapSubmonoid A M))).comp
    (FixedPoints.subring A G).subtype).codRestrict _ (algebraMap_mem_fixedPoints M)).toAlgebra

/-- The algebra map `Aᴳ → (M⁻¹A)ᴳ` is the localization map `A → M⁻¹A`. -/
@[simp]
theorem coe_algebraMap_localization (a : FixedPoints.subring A G) :
    (algebraMap (FixedPoints.subring A G)
        (FixedPoints.subring (Localization (Algebra.algebraMapSubmonoid A M)) G) a :
      Localization (Algebra.algebraMapSubmonoid A M)) =
      algebraMap A (Localization (Algebra.algebraMapSubmonoid A M)) a :=
  rfl

/-- **Invariants commute with localization at invariant elements.** For a finite group `G` and a
submonoid `M` of the invariants `Aᴳ`, the invariants of `M⁻¹A` are the localization of `Aᴳ`
at `M`. -/
instance isLocalization [Finite G] :
    IsLocalization M (FixedPoints.subring (Localization (Algebra.algebraMapSubmonoid A M)) G) :=
  isLocalization_of_mem_range_iff M (MulSemiringAction.toRingHom G A)
    (MulSemiringAction.toRingHom G _) (smul_algebraMap_localization M) Subtype.val_injective
    (fun a ↦ ⟨fun ⟨b, hb⟩ ↦ hb ▸ b.2, fun ha ↦ ⟨⟨a, ha⟩, rfl⟩⟩) Subtype.val_injective
    (fun s ↦ ⟨fun ⟨b, hb⟩ ↦ hb ▸ b.2, fun hs ↦ ⟨⟨s, hs⟩, rfl⟩⟩) fun _ ↦ rfl

end Localization

section LocalRingHom

variable [Finite G]

/-- **Prime avoidance for the translates of a prime.** For a finite group `G`, if an ideal `I`
of `A` is contained in no translate `g⁻¹ • Q` of a prime `Q`, then some `u ∈ I` satisfies
`g • u ∉ Q` for every `g`. -/
theorem _root_.Ideal.exists_mem_forall_smul_notMem (Q : Ideal A) [Q.IsPrime] {I : Ideal A}
    (hI : ∀ g : G, ¬ I ≤ Q.comap (MulSemiringAction.toRingHom G A g)) :
    ∃ u ∈ I, ∀ g : G, g • u ∉ Q := by
  have := Fintype.ofFinite G
  by_contra! h
  have hsub : (I : Set A) ⊆ ⋃ g ∈ (Finset.univ : Finset G),
      (Q.comap (MulSemiringAction.toRingHom G A g) : Set A) := fun u hu ↦ by
    obtain ⟨g, hg⟩ := h u hu
    exact Set.mem_biUnion (Finset.mem_coe.mpr (Finset.mem_univ g)) hg
  obtain ⟨g, -, hg⟩ := (Ideal.subset_union_prime 1 1
    (fun g _ _ _ ↦ Ideal.comap_isPrime _ Q)).mp hsub
  exact hI g hg

/-- **Norms of elements avoiding every translate of a prime.** For a finite group `G`, if
`g • u ∉ Q` for every `g`, then the invariant norm `∏ g, g • u` lies outside `Q` and is divisible
by `u`. -/
theorem _root_.Ideal.exists_notMem_dvd_of_forall_smul_notMem (Q : Ideal A) [Q.IsPrime] {u : A}
    (hu : ∀ g : G, g • u ∉ Q) : ∃ r : FixedPoints.subring A G, (r : A) ∉ Q ∧ u ∣ r := by
  have := Fintype.ofFinite G
  refine ⟨⟨∏ g : G, g • u, fun g ↦ Finset.smul_prod_perm u g⟩, fun hmem ↦ ?_, ?_⟩
  · obtain ⟨g, -, hg⟩ := (Ideal.IsPrime.prod_mem_iff (p := Q)).mp hmem
    exact hu g hg
  · simpa using Finset.dvd_prod_of_mem (fun g : G ↦ g • u) (Finset.mem_univ 1)

/-- If an invariant `x` is killed by an element outside a prime `Q`, it is killed by an invariant
element outside `Q`. This is prime avoidance for the `G`-stable annihilator of `x` and the
finitely many primes `g⁻¹ • Q`. -/
theorem exists_mul_eq_zero_of_mul_eq_zero (Q : Ideal A) [Q.IsPrime] (x : FixedPoints.subring A G)
    {t : A} (htQ : t ∉ Q) (htx : t * x = 0) :
    ∃ s ∈ FixedPoints.subring A G, s ∉ Q ∧ s * x = 0 := by
  set I : Ideal A := (Ideal.span {(x : A)}).annihilator
  have hI (u : A) : u ∈ I ↔ u * x = 0 := by
    rw [Submodule.mem_annihilator_span_singleton, smul_eq_mul]
  obtain ⟨u, huI, hu⟩ := Q.exists_mem_forall_smul_notMem (G := G) (I := I) fun g hg ↦ by
    -- The annihilator of `x` is `G`-stable, so it contains `g⁻¹ • t`, and then `t ∈ Q`.
    have hmem : g⁻¹ • t ∈ I := by
      rw [hI, ← x.2 g⁻¹, ← smul_mul', htx, smul_zero]
    exact htQ (by simpa using hg hmem)
  obtain ⟨r, hrQ, c, hc⟩ := Q.exists_notMem_dvd_of_forall_smul_notMem hu
  exact ⟨r, r.2, hrQ, by rw [hc, mul_comm u, mul_assoc, (hI u).mp huI, mul_zero]⟩

/-- **Invariants inject into stalks.** For a finite group `G`, a prime `Q` of `A` and the prime
`P` of `Aᴳ` below it, the induced homomorphism of local rings `(Aᴳ)_P → A_Q` is injective. -/
theorem localRingHom_injective (P : Ideal (FixedPoints.subring A G)) (Q : Ideal A) [P.IsPrime]
    [Q.IsPrime] (hPQ : P = Q.comap (algebraMap (FixedPoints.subring A G) A)) :
    Function.Injective
      (Localization.localRingHom P Q (algebraMap (FixedPoints.subring A G) A) hPQ) := by
  refine IsLocalization.injective_of_map_algebraMap_zero (M := P.primeCompl) _ _ fun x hx ↦ ?_
  rw [Localization.localRingHom_to_map,
    IsLocalization.map_eq_zero_iff Q.primeCompl] at hx
  obtain ⟨⟨t, htQ⟩, htx⟩ := hx
  obtain ⟨s, hs, hsQ, hsx⟩ := exists_mul_eq_zero_of_mul_eq_zero Q x htQ htx
  refine (IsLocalization.map_eq_zero_iff P.primeCompl _ x).mpr
    ⟨⟨⟨s, hs⟩, fun h ↦ hsQ (by rwa [hPQ] at h)⟩, Subtype.ext hsx⟩

end LocalRingHom

end TauCeti.FixedPoints
