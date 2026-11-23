/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.NumberField.ExtensionDiscriminant
public import Mathlib.RingTheory.Localization.Integer

/-!
# Localization of extension discriminants

For compatible localizations `SA` of `A` at `S` and `SB` of `B` at the image of `S`,
extending scalars of the extension discriminant submodule from `A` to `SA` gives the
extension discriminant computed over the localized base.

## Source correspondence

The source is Andrew V. Sutherland, *18.785 Number Theory I*, Lecture 12,
[Proposition 12.15](https://math.mit.edu/classes/18.785/2021fa/LectureNotes12.pdf#page=5):
for the usual `AKLB` setup and a multiplicative subset `S ⊆ A`,
`S⁻¹ D_{B/A} = D_{S⁻¹B/S⁻¹A}`.

The Lean statement maps its clauses as follows.

* `IsLocalization S SA` realizes `SA = S⁻¹A`, while
  `IsLocalization (Algebra.algebraMapSubmonoid B S) SB` realizes
  `SB = S⁻¹B`; the scalar-tower instances assert compatibility of all maps into
  the ambient fields `K` and `L`.
* `Submodule.span SA (extensionDiscriminant A K L B : Set K)` is the scalar extension
  `S⁻¹ D_{B/A}`, and `extensionDiscriminant SA K L SB` is
  `D_{S⁻¹B/S⁻¹A}`.
* `FiniteDimensional K L` supplies the finite tuple size and field trace used by the
  discriminant.  The forward inclusion scales tuples into the localization; the reverse
  inclusion follows the source proof by choosing one common denominator and applying
  `discr_smul`, the identity `disc(a • e) = a^(2n) disc(e)`.
* The source's Dedekind, fraction-ring, integral-closure, module-finiteness,
  torsion-freeness, and separability assumptions ensure its traditional number-field
  setting.  They are not used by this identity once the compatible localization towers
  and finite-dimensional trace are supplied, so the Lean theorem genuinely generalizes
  Proposition 12.15 to the commutative-ring setting above.
-/

@[expose] public section

set_option autoImplicit false

universe u

/-- Discriminant of a uniformly scaled tuple. -/
private theorem discr_smul {K L : Type*} [Field K] [Field L] [Algebra K L]
    (c : K) (b : Fin (Module.finrank K L) → L) :
    Algebra.discr K (fun i => c • b i) =
      c ^ (2 * Module.finrank K L) * Algebra.discr K b := by
  simp only [Algebra.discr_def]
  have hM : Algebra.traceMatrix K (fun i => c • b i) =
      c ^ 2 • Algebra.traceMatrix K b := by
    ext i j
    simp only [Algebra.traceMatrix_apply, Algebra.traceForm_apply,
      Matrix.smul_apply, smul_eq_mul]
    rw [smul_mul_smul_comm]
    simp [map_smul, smul_eq_mul, sq]
  rw [hM, Matrix.det_smul]
  simp only [Fintype.card_fin]
  ring

/-- The image of `B` in `L` lands in the image of the localized order `SB`. -/
private theorem image_subset (A : Type*) (L : Type u) (B SA SB : Type*)
    [CommRing A] [CommRing B] [CommRing SA] [CommRing SB] [Field L]
    [Algebra A B] [Algebra B L] [Algebra A L] [IsScalarTower A B L]
    [Algebra SA SB] [Algebra SB L] [Algebra SA L] [IsScalarTower SA SB L]
    [Algebra B SB] [IsScalarTower B SB L] :
    (imageOfB A L B : Set L) ⊆ (imageOfB SA L SB : Set L) := by
  intro x hx
  have hx' : x ∈ imageOfB A L B := hx
  rw [mem_imageOfB A L B] at hx'
  obtain ⟨b, rfl⟩ := hx'
  change algebraMap B L b ∈ imageOfB SA L SB
  rw [mem_imageOfB SA L SB]
  exact ⟨algebraMap B SB b, (IsScalarTower.algebraMap_apply B SB L b).symm⟩

/-- Discriminant generators over `B` are discriminant generators over `SB`. -/
private theorem discr_set_subset (A K : Type*) (L : Type u) (B SA SB : Type*)
    [CommRing A] [Field K] [CommRing B] [Field L] [CommRing SA] [CommRing SB]
    [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
    [IsScalarTower A K L] [IsScalarTower A B L] [FiniteDimensional K L]
    [Algebra SA K] [Algebra SB L] [Algebra SA SB] [Algebra SA L]
    [IsScalarTower SA K L] [IsScalarTower SA SB L]
    [Algebra B SB] [IsScalarTower B SB L] :
    latticeDiscriminantSet A K (imageOfB A L B) ⊆
      latticeDiscriminantSet SA K (imageOfB SA L SB) := by
  intro d hd
  simp only [latticeDiscriminantSet, Set.mem_ofPred_eq] at hd ⊢
  obtain ⟨b, hb, rfl⟩ := hd
  refine ⟨b, fun i => SetLike.mem_coe.mp ?_, rfl⟩
  exact image_subset A L B SA SB (SetLike.mem_coe.mpr (hb i))

section Localization

variable (A K : Type*) (L : Type u) (B : Type*)
  [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [FiniteDimensional K L]

variable (S : Submonoid A)

variable (SA : Type*) [CommRing SA] [Algebra A SA] [IsLocalization S SA]
variable (SB : Type*) [CommRing SB] [Algebra B SB]
  [IsLocalization (Algebra.algebraMapSubmonoid B S) SB]

variable [Algebra SA K] [Algebra SB L] [Algebra SA SB] [Algebra SA L]
variable [IsScalarTower SA K L] [IsScalarTower SA SB L]
variable [IsScalarTower A SA K] [IsScalarTower B SB L]

include S in
/--
**Localization of the extension discriminant.** Let $A$ and $B$ be commutative rings and $K$
and $L$ fields, with ring maps $A \to K \to L$ and $A \to B \to L$ whose composites $A \to L$
agree, and with $L$ finite-dimensional over $K$ of degree $n$. Write $D_{B/A}$ for the
$A$-submodule of $K$ generated by the discriminants $\operatorname{disc}_{L/K}(b_1, \dots, b_n)$
of all $n$-tuples of elements of the image of $B$ in $L$. Let $S$ be a submonoid of $A$, let
$S^{-1}A$ be a localization of $A$ at $S$, and let $S^{-1}B$ be a localization of $B$ at the
image of $S$ in $B$. Suppose given ring maps $S^{-1}A \to K$, $S^{-1}A \to S^{-1}B$ and
$S^{-1}B \to L$ such that the composite $A \to S^{-1}A \to K$ is the map $A \to K$, the
composite $B \to S^{-1}B \to L$ is the map $B \to L$, and the composites
$S^{-1}A \to K \to L$ and $S^{-1}A \to S^{-1}B \to L$ agree. Then the $S^{-1}A$-submodule of
$K$ spanned by $D_{B/A}$ equals $D_{S^{-1}B/S^{-1}A}$, the $S^{-1}A$-submodule of $K$ generated
by the discriminants of $n$-tuples of elements of the image of $S^{-1}B$ in $L$.

No Dedekind, fraction-ring, integrally-closed, or separability hypotheses are used.
-/
theorem extensionDiscriminant_localization :
    Submodule.span SA (extensionDiscriminant A K L B : Set K) =
      extensionDiscriminant SA K L SB := by
  rw [extensionDiscriminant_eq A K L B, extensionDiscriminant_eq SA K L SB]
  simp only [latticeDiscriminant]
  apply le_antisymm
  · rw [Submodule.span_span_of_tower]
    exact Submodule.span_mono (discr_set_subset A K L B SA SB)
  · apply Submodule.span_le.mpr
    intro d hd
    simp only [latticeDiscriminantSet, Set.mem_ofPred_eq] at hd
    obtain ⟨e, he, rfl⟩ := hd
    have hsb : ∀ i, ∃ sb : SB, algebraMap SB L sb = e i :=
      fun i => (mem_imageOfB SA L SB).mp (he i)
    choose sb hsb using hsb
    obtain ⟨t, ht⟩ := IsLocalization.exist_integer_multiples
      (Algebra.algebraMapSubmonoid B S) Finset.univ sb
    choose bi hbi using fun i => ht i (Finset.mem_univ i)
    obtain ⟨a, haS, hat⟩ := Submonoid.mem_map.mp t.property
    have hL : ∀ i, algebraMap B L (bi i) = algebraMap A L a * e i := by
      intro i
      have h1 := congr_arg (algebraMap SB L) (hbi i)
      rw [← IsScalarTower.algebraMap_apply B SB L] at h1
      simp only [Algebra.smul_def, map_mul,
        ← IsScalarTower.algebraMap_apply B SB L] at h1
      rw [hat.symm, ← IsScalarTower.algebraMap_apply A B L, hsb i] at h1
      exact h1
    have hsmul_mem : ∀ i, algebraMap A K a • e i ∈ imageOfB A L B := by
      intro i
      rw [mem_imageOfB A L B]
      refine ⟨bi i, ?_⟩
      rw [hL i, Algebra.smul_def, IsScalarTower.algebraMap_apply A K L]
    have hdisc_mem : Algebra.discr K (fun i => algebraMap A K a • e i) ∈
        extensionDiscriminant A K L B :=
      discr_mem_extensionDiscriminant A K L B hsmul_mem
    have hdisc_eq : Algebra.discr K (fun i => algebraMap A K a • e i) =
        (algebraMap A K a) ^ (2 * Module.finrank K L) * Algebra.discr K e :=
      discr_smul (algebraMap A K a) e
    have ha_unit : IsUnit (algebraMap A SA a) :=
      IsLocalization.map_units SA ⟨a, haS⟩
    have ha_ne : algebraMap A K a ≠ 0 := by
      rw [IsScalarTower.algebraMap_apply A SA K]
      exact (ha_unit.map (algebraMap SA K)).ne_zero
    have hdisc_inv : Algebra.discr K e =
        ((algebraMap A K a) ^ (2 * Module.finrank K L))⁻¹ *
          Algebra.discr K (fun i => algebraMap A K a • e i) := by
      rw [hdisc_eq]
      rw [inv_mul_cancel_left₀ (pow_ne_zero _ ha_ne)]
    obtain ⟨u, hu⟩ := ha_unit
    have hmap_inv : algebraMap SA K (↑(u⁻¹) : SA) = (algebraMap SA K (u : SA))⁻¹ :=
      eq_inv_of_mul_eq_one_right (by
        rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one])
    have hinv_eq : ((algebraMap A K a) ^ (2 * Module.finrank K L))⁻¹ =
        algebraMap SA K ((↑u⁻¹ : SA) ^ (2 * Module.finrank K L)) := by
      rw [map_pow, hmap_inv, ← inv_pow, hu,
        IsScalarTower.algebraMap_apply A SA K]
    rw [hdisc_inv, hinv_eq, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    exact Submodule.smul_mem _ _
      (Submodule.subset_span (SetLike.mem_coe.mpr hdisc_mem))

end Localization
