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
TauCeti/RingTheory/CyclicCohomology/Periodicity/Basic.lean
Public source: https://github.com/TauCetiProject/TauCeti
The original contributors' copyright, author and Apache License 2.0
notice is retained above. Modification notice: use the explicitly
listed MathlibExt ports for this complete SBI dependency closure;
retain the mathematical declarations and original names. Identity-scalar
multilinear maps and endomorphism-application lemmas use the pinned
Mathlib API; the finite-coordinate port keeps only its four needed lemmas.
-/
module

public import MathlibExt.RingTheory.CyclicBicomplex
public import MathlibExt.RingTheory.CyclicHochschildComparison
public import MathlibExt.Algebra.Homology.CyclicNatReindexing
public import MathlibExt.Algebra.Homology.CyclicHomologyExtension

/-!
# The periodicity map of the cyclic bicomplex

The differentials of Connes' cyclic bicomplex only depend on the parity of the column
(`TauCeti.cyclicBicomplexHorizontal_add_two`, `TauCeti.cyclicBicomplexVertical_add_two`). Hence
moving every component of a total cochain two columns to the right is a cochain map from the total
complex, shifted two degrees up, to itself. In the row-indexed description of
`TauCeti.RingTheory.CyclicCohomology.Bicomplex`, where a total cochain of degree `m` is a family
`(x_q)_q` with `x_q = 0` for `q > m`, this map is the identity on families: a total cochain of
degree `m` is also one of degree `m + 2`, its component `x_q` now sitting in column `m + 2 - q`.
The induced map `S : H^m(Tot) → H^(m+2)(Tot)` is the periodicity map of the bicomplex. Its
cokernel is the total complex of the first two columns, the Hochschild complex `(C, b)` and the
bar complex `(C, -b')`.

Projecting a total cochain of degree `m` onto its column-zero component `x_m` is a cochain map
from the total complex to the Hochschild cochain complex, whose restriction to Connes' cyclic
cochain complex is the inclusion `TauCeti.cyclicCochainComplexι`. On cohomology it is the map
`I : H^m(Tot) → HH^m(A, Hom_R(A, M))` of the bicomplex. Since `S` lands in the columns `≥ 2`, the
composite `I ∘ S` vanishes already on cochains. For a unital algebra the contraction
`s φ = φ(1, -)` of the bar complex shows that conversely every class killed by `I` comes from
`S`, so

`H^m(Tot) → H^(m+2)(Tot) → HH^(m+2)(A, Hom_R(A, M))`

is exact. This is one of the three exactness statements of Connes' SBI sequence, in the bicomplex
model. Over a ring containing `ℚ`, the total cohomology is cyclic cohomology
(`TauCeti.quasiIso_cyclicCochainComplexToTotal`), and the composite of this identification with
`I` is the map `TauCeti.cyclicCohomology.toHochschild`.

The shift of total cochains and the projection onto column zero, together with their support
formulas, require only additive commutative monoids of coefficients.

The periodicity map here is the shift of columns of the bicomplex. Connes' operator `S` is
instead normalized as the exterior product with the cyclic `2`-cocycle `(a₀, a₁, a₂) ↦ a₀a₁a₂`;
no comparison of the two normalizations is made here.

## Main definitions

* `TauCeti.cyclicTotalPeriodicity`: the periodicity map `Tot^m → Tot^(m+2)` on total cochains.
* `TauCeti.cyclicTotalComplexPeriodicity`: the periodicity cochain map from the total complex
  shifted two degrees up to the total complex.
* `TauCeti.cyclicTotalHomologyPeriodicity`: the periodicity map `S : H^m(Tot) → H^(m+2)(Tot)`.
* `TauCeti.cyclicTotalToHochschild`, `TauCeti.cyclicTotalComplexToHochschild`: the projection onto
  column zero, and the resulting cochain map to the Hochschild cochain complex.

## Main results

* `TauCeti.cyclicTotalDifferential_cyclicTotalPeriodicity`: the periodicity map commutes with the
  total differential.
* `TauCeti.cyclicCochainComplexToTotal_comp_cyclicTotalComplexToHochschild`: on cyclic cochains
  the projection onto column zero is the inclusion into Hochschild cochains.
* `TauCeti.cyclicTotalComplexPeriodicity_comp_cyclicTotalComplexToHochschild`: `I ∘ S = 0` on
  cochains.
* `TauCeti.exists_cyclicTotalPeriodicity_eq_add_cyclicTotalDifferential`: for a unital algebra, a
  total cochain vanishing in column zero whose column-one component is a bar cocycle lies in the
  image of the periodicity map up to a total coboundary.
* `TauCeti.cyclicTotalHomologyPeriodicity_homologyπ`: `S` sends the class of a total cocycle of
  degree `m` to the class of the same family of cochains in degree `m + 2`.
* `TauCeti.homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMk`,
  `TauCeti.cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMk`: `I` and `S` on classes of total
  cocycles.
* `TauCeti.homologyMap_cyclicCochainComplexToTotal_comp_homologyMap_cyclicTotalComplexToHochschild`:
  `I` on cyclic cohomology factors through the cohomology of the total complex.
* `TauCeti.exact_cyclicTotalHomologyPeriodicity_homologyMap_cyclicTotalComplexToHochschild`: for a
  unital algebra, `H^m(Tot) → H^(m+2)(Tot) → HH^(m+2)` is exact.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
* J.-L. Loday, *Cyclic Homology*, §§2.1–2.2.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti

universe u

/-! ### The periodicity map on total cochains -/

section Cochains

variable {R A M : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A] [AddCommMonoid M]
  [Module R M]

variable (R A M) in
/-- The periodicity map `Tot^m → Tot^(m+2)` of the cyclic bicomplex. It is the identity on
families of cochains: the component in row `q` moves from column `m - q` to column `m + 2 - q`. -/
def cyclicTotalPeriodicity (m : ℕ) :
    cyclicTotalCochains R A M m →ₗ[R] cyclicTotalCochains R A M (m + 2) :=
  Submodule.inclusion (cyclicTotalCochains_mono (Nat.le_add_right m 2))

/-- The periodicity map does not change the family of cochains. -/
@[simp]
theorem coe_cyclicTotalPeriodicity_apply {m : ℕ} (x : cyclicTotalCochains R A M m) :
    (cyclicTotalPeriodicity R A M m x : ∀ q : ℕ, MultilinearMap (RingHom.id R) (fun _ : Fin (q + 1)
        ↦ A) M) =
      x :=
  (rfl)

variable (R A M) in
/-- The periodicity map is injective. -/
theorem cyclicTotalPeriodicity_injective (m : ℕ) :
    Function.Injective (cyclicTotalPeriodicity R A M m) :=
  Submodule.inclusion_injective _

/-- A total cochain of degree `m + 2` lies in the image of the periodicity map exactly when its
components in columns zero and one, the rows `m + 2` and `m + 1`, vanish. -/
theorem mem_range_cyclicTotalPeriodicity_iff {m : ℕ} {x : cyclicTotalCochains R A M (m + 2)} :
    x ∈ LinearMap.range (cyclicTotalPeriodicity R A M m) ↔ x.1 (m + 1) = 0 ∧ x.1 (m + 2) = 0 := by
  refine ⟨?_, fun ⟨h₁, h₂⟩ ↦ ⟨⟨x.1, ?_⟩, rfl⟩⟩
  · rintro ⟨y, rfl⟩
    exact ⟨mem_cyclicTotalCochains_iff.1 y.2 _ (by omega),
      mem_cyclicTotalCochains_iff.1 y.2 _ (by omega)⟩
  · refine mem_cyclicTotalCochains_iff.2 fun q hq ↦ ?_
    obtain rfl | rfl | hq : q = m + 1 ∨ q = m + 2 ∨ m + 2 < q := by omega
    · exact h₁
    · exact h₂
    · exact mem_cyclicTotalCochains_iff.1 x.2 q hq

/-! ### The projection onto column zero -/

variable (R A M) in
/-- The projection of a total cochain of degree `m` onto its component in column zero, the
Hochschild `m`-cochain in row `m`. -/
def cyclicTotalToHochschild (m : ℕ) :
    cyclicTotalCochains R A M m →ₗ[R] MultilinearMap (RingHom.id R) (fun _ : Fin (m + 1) ↦ A) M :=
  LinearMap.proj m ∘ₗ (cyclicTotalCochains R A M m).subtype

/-- The projection onto column zero takes the component in row `m`. -/
@[simp]
theorem cyclicTotalToHochschild_apply {m : ℕ} (x : cyclicTotalCochains R A M m) :
    cyclicTotalToHochschild R A M m x = x.1 m :=
  (rfl)

/-- The projection onto column zero vanishes on the image of the periodicity map. -/
theorem cyclicTotalToHochschild_cyclicTotalPeriodicity {m : ℕ}
    (x : cyclicTotalCochains R A M m) :
    cyclicTotalToHochschild R A M (m + 2) (cyclicTotalPeriodicity R A M m x) = 0 := by
  simp

end Cochains

section CyclicOperators

variable {R A M : Type*} [CommSemiring R] [AddCommMonoid A] [Module R A] [AddCommGroup M]
  [Module R M]

/-- The projection onto column zero of a cyclic cochain included into column zero is the cochain
itself. -/
theorem cyclicTotalToHochschild_cyclicCochainsToTotal {m : ℕ} (φ : cyclicCochains R A M m) :
    cyclicTotalToHochschild R A M m (cyclicCochainsToTotal R A M m φ) = φ := by
  rw [cyclicTotalToHochschild_apply, coe_cyclicCochainsToTotal_apply, Pi.single_eq_same]

/-- Moving the component of a total cochain of degree `m` in row `k` two columns to the right
does not change its horizontal differential. -/
private theorem cyclicBicomplexHorizontal_sub_apply {m : ℕ} (x : cyclicTotalCochains R A M m)
    (k : ℕ) :
    cyclicBicomplexHorizontal R A M (m + 2 - k) k (x.1 k) =
      cyclicBicomplexHorizontal R A M (m - k) k (x.1 k) := by
  by_cases hk : k ≤ m
  · rw [Nat.sub_add_comm hk, cyclicBicomplexHorizontal_add_two]
  · rw [mem_cyclicTotalCochains_iff.1 x.2 k (by omega), map_zero, map_zero]

end CyclicOperators

section Differential

variable {R A M : Type*} [CommSemiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- Moving the component of a total cochain of degree `m` in row `k` two columns to the right
does not change its vertical differential. -/
private theorem cyclicBicomplexVertical_sub_apply {m : ℕ} (x : cyclicTotalCochains R A M m)
    (k : ℕ) :
    cyclicBicomplexVertical R A M (m + 2 - k) k (x.1 k) =
      cyclicBicomplexVertical R A M (m - k) k (x.1 k) := by
  by_cases hk : k ≤ m
  · rw [Nat.sub_add_comm hk, cyclicBicomplexVertical_add_two]
  · rw [mem_cyclicTotalCochains_iff.1 x.2 k (by omega), map_zero, map_zero]

/-- The periodicity map commutes with the total differential. -/
@[simp]
theorem cyclicTotalDifferential_cyclicTotalPeriodicity {m : ℕ} (x : cyclicTotalCochains R A M m) :
    cyclicTotalDifferential R A M (m + 2) (cyclicTotalPeriodicity R A M m x) =
      cyclicTotalPeriodicity R A M (m + 1) (cyclicTotalDifferential R A M m x) := by
  apply Subtype.ext
  funext q
  cases q with
  | zero =>
    simp only [cyclicTotalDifferential_apply_zero, coe_cyclicTotalPeriodicity_apply,
      cyclicBicomplexHorizontal_add_two]
  | succ q =>
    simp only [cyclicTotalDifferential_apply_succ, coe_cyclicTotalPeriodicity_apply]
    rw [cyclicBicomplexVertical_sub_apply x q, ← cyclicBicomplexHorizontal_sub_apply x (q + 1)]

/-- The projection onto column zero commutes with the differentials: the column-zero component of
the total differential of `x` is the Hochschild coboundary of the column-zero component of `x`. -/
theorem cyclicTotalToHochschild_cyclicTotalDifferential {m : ℕ}
    (x : cyclicTotalCochains R A M m) :
    cyclicTotalToHochschild R A M (m + 1) (cyclicTotalDifferential R A M m x) =
      hochschildCoboundary R A M m (cyclicTotalToHochschild R A M m x) := by
  rw [cyclicTotalToHochschild_apply, cyclicTotalDifferential_apply_succ, Nat.sub_self,
    cyclicBicomplexVertical_of_even Even.zero, mem_cyclicTotalCochains_iff.1 x.2 (m + 1) (by omega),
    map_zero, add_zero, cyclicTotalToHochschild_apply]

end Differential

section KillingColumnOne

variable {R A M : Type*} [CommSemiring R] [NonAssocSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- **Killing column one.** Let `y` be a total cochain of degree `m + 2` of a unital algebra which
vanishes in column zero and whose column-one component is a cocycle for the bar coboundary. Since
the contraction `s` gives `y (m + 1) = b' (s (y (m + 1)))`, adding the total differential of
`s (y (m + 1))`, placed in column one, moves `y` into the image of the periodicity map. -/
theorem exists_cyclicTotalPeriodicity_eq_add_cyclicTotalDifferential {m : ℕ}
    (y : cyclicTotalCochains R A M (m + 2)) (hy₂ : y.1 (m + 2) = 0)
    (hy₁ : barCoboundary R A M (m + 1) (y.1 (m + 1)) = 0) :
    ∃ w z, cyclicTotalPeriodicity R A M m w = y + cyclicTotalDifferential R A M (m + 1) z := by
  let z : cyclicTotalCochains R A M (m + 1) :=
    ⟨Pi.single m (barContraction R A M m (y.1 (m + 1))),
      single_mem_cyclicTotalCochains (Nat.le_succ m) _⟩
  have hz₁ : (cyclicTotalDifferential R A M (m + 1) z).1 (m + 1) = -y.1 (m + 1) := by
    have h := barCoboundary_barContraction_add_barContraction_barCoboundary (y.1 (m + 1))
    rw [hy₁, map_zero, add_zero] at h
    simp [z, h]
  have hz₂ : (cyclicTotalDifferential R A M (m + 1) z).1 (m + 2) = 0 := by
    have hne : m + 1 + 1 ≠ m := by omega
    simp [z, Pi.single_eq_of_ne hne]
  obtain ⟨w, hw⟩ := (mem_range_cyclicTotalPeriodicity_iff
    (x := y + cyclicTotalDifferential R A M (m + 1) z)).2 ⟨by simp [hz₁], by simp [hz₂, hy₂]⟩
  exact ⟨w, z, hw⟩

end KillingColumnOne

section Contraction

variable {R A M : Type*} [CommRing R] [Semiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- **Killing the first two columns.** Let `x` be a total cocycle of degree `m + 2` of a unital
algebra whose column-zero component is the Hochschild coboundary of a cochain `χ`. Then `x` is
the sum of the image under the periodicity map of a total cochain of degree `m` and a total
coboundary. -/
private theorem exists_eq_cyclicTotalPeriodicity_add_cyclicTotalDifferential {m : ℕ}
    (x : cyclicTotalCochains R A M (m + 2)) (hx : cyclicTotalDifferential R A M (m + 2) x = 0)
    (χ : MultilinearMap (RingHom.id R) (fun _ : Fin (m + 2) ↦ A) M)
    (hχ : hochschildCoboundary R A M (m + 1) χ = x.1 (m + 2)) :
    ∃ w b, x.1 =
      (cyclicTotalPeriodicity R A M m w).1 + (cyclicTotalDifferential R A M (m + 1) b).1 := by
  -- The statement compares underlying families, since the total differential of a cochain of
  -- degree `m + 1` lands in `cyclicTotalCochains R A M (m + 1 + 1)` rather than in degree `m + 2`.
  -- the cochain `χ` in column zero, and the remainder `y = x - D χ`
  let c : cyclicTotalCochains R A M (m + 1) :=
    ⟨Pi.single (m + 1) χ, single_mem_cyclicTotalCochains le_rfl χ⟩
  let y : cyclicTotalCochains R A M (m + 2) := x - cyclicTotalDifferential R A M (m + 1) c
  have hc₂ : (cyclicTotalDifferential R A M (m + 1) c).1 (m + 2) = x.1 (m + 2) := by
    simp [c, hχ]
  have hy₂ : y.1 (m + 2) = 0 := by
    simp only [y, Submodule.coe_sub, Pi.sub_apply, hc₂, sub_self]
  -- the component `y` in column one is a cocycle for the bar coboundary
  have hy₁ : barCoboundary R A M (m + 1) (y.1 (m + 1)) = 0 := by
    have hx' := congrArg (fun z ↦ z.1 (m + 2)) hx
    have hc₁ : (cyclicTotalDifferential R A M (m + 1) c).1 (m + 1) =
        χ - cyclicOperator R A M (m + 1) χ := by
      simp [c]
    have hb := LinearMap.congr_fun
      (one_sub_cyclicOperator_comp_hochschildCoboundary R A M (m + 1)) χ
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, Module.End.one_apply, hχ] at hb
    simp only [cyclicTotalDifferential_apply_succ, Submodule.coe_zero, Pi.zero_apply] at hx'
    -- the rows `m + 1` and `m + 2` of a total cochain of degree `m + 2` sit in columns one and zero
    have h₁ : m + 2 - (m + 1) = 1 := by omega
    have h₀ : m + 2 - (m + 1 + 1) = 0 := Nat.sub_self _
    rw [h₁, h₀, cyclicBicomplexVertical_of_odd odd_one,
      cyclicBicomplexHorizontal_of_even Even.zero] at hx'
    simp only [LinearMap.neg_apply, LinearMap.sub_apply, Module.End.one_apply] at hx'
    simp only [y, Submodule.coe_sub, Pi.sub_apply, map_sub, hc₁, ← hb]
    exact sub_eq_zero.2 (neg_add_eq_zero.1 hx')
  -- killing column one of `y` leaves a total cochain in the image of the periodicity map
  obtain ⟨w, z, hw⟩ := exists_cyclicTotalPeriodicity_eq_add_cyclicTotalDifferential y hy₂ hy₁
  refine ⟨w, c - z, ?_⟩
  rw [hw, map_sub]
  simp only [y, Submodule.coe_sub, Submodule.coe_add]
  abel

end Contraction

/-! ### The cochain maps and the exactness of `H^m(Tot) → H^(m+2)(Tot) → HH^(m+2)` -/

section Complex

variable (R : Type*) (A : Type u) (M : Type*) [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- The periodicity cochain map of the cyclic bicomplex, from the total complex shifted two degrees
up to the total complex. In degree `m + 2` it is the periodicity map `Tot^m → Tot^(m+2)`; the
shifted complex vanishes in degrees zero and one. -/
def cyclicTotalComplexPeriodicity :
    (cyclicTotalComplex R A M).extend (ComplexShape.embeddingUpNatAdd 2) ⟶
      cyclicTotalComplex R A M where
  f
    | 0 => 0
    | 1 => 0
    | m + 2 =>
      ((cyclicTotalComplex R A M).extendXIso _ (ComplexShape.embeddingUpNatAdd_f 2 m)).hom ≫
        (cyclicTotalComplexXIso R A M m).hom ≫ ModuleCat.ofHom (cyclicTotalPeriodicity R A M m) ≫
          (cyclicTotalComplexXIso R A M (m + 2)).inv
  comm' := by
    rintro i _ rfl
    match i with
    | 0 =>
      exact (HomologicalComplex.isZero_extend_X _ _ 0 fun _ ↦ by simp).eq_of_src _ _
    | 1 =>
      exact (HomologicalComplex.isZero_extend_X _ _ 1 fun _ ↦ by simp).eq_of_src _ _
    | m + 2 =>
      rw [Nat.add_right_comm m 2 1, HomologicalComplex.extend_d_eq _ _
        (ComplexShape.embeddingUpNatAdd_f 2 m) (ComplexShape.embeddingUpNatAdd_f 2 (m + 1))]
      dsimp only
      refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
      apply (ModuleCat.mono_iff_injective (cyclicTotalComplexXIso R A M (m + 3)).hom).1
        inferInstance
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply, cyclicTotalComplex_d_apply,
        Iso.inv_hom_id_apply, ModuleCat.hom_ofHom]
      exact cyclicTotalDifferential_cyclicTotalPeriodicity _

/-- Under the identifications of the terms with modules of total cochains, the periodicity cochain
map is the periodicity map in degree `m + 2`. -/
@[reassoc, elementwise]
theorem cyclicTotalComplexPeriodicity_f (m : ℕ) :
    (cyclicTotalComplexPeriodicity R A M).f (m + 2) ≫
        (cyclicTotalComplexXIso R A M (m + 2)).hom =
      ((cyclicTotalComplex R A M).extendXIso _ (ComplexShape.embeddingUpNatAdd_f 2 m)).hom ≫
        (cyclicTotalComplexXIso R A M m).hom ≫
          ModuleCat.ofHom (cyclicTotalPeriodicity R A M m) := by
  simp [cyclicTotalComplexPeriodicity]

/-- The periodicity map `S : H^m(Tot) → H^(m+2)(Tot)` of the cyclic bicomplex. -/
def cyclicTotalHomologyPeriodicity (m : ℕ) :
    (cyclicTotalComplex R A M).homology m ⟶ (cyclicTotalComplex R A M).homology (m + 2) :=
  ((cyclicTotalComplex R A M).extendHomologyIso (ComplexShape.embeddingUpNatAdd 2)
      (ComplexShape.embeddingUpNatAdd_f 2 m)).inv ≫
    HomologicalComplex.homologyMap (cyclicTotalComplexPeriodicity R A M) (m + 2)

/-- The cochain map from the total complex to the Hochschild cochain complex projecting a total
cochain onto its component in column zero. -/
def cyclicTotalComplexToHochschild :
    cyclicTotalComplex R A M ⟶ hochschildCochainComplex R A M where
  f m := (cyclicTotalComplexXIso R A M m).hom ≫ ModuleCat.ofHom (cyclicTotalToHochschild R A M m) ≫
    (hochschildCochainComplexXIso R A M m).inv
  comm' := by
    rintro m _ rfl
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    apply (ModuleCat.mono_iff_injective (hochschildCochainComplexXIso R A M (m + 1)).hom).1
      inferInstance
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hochschildCochainComplex_d_apply,
      cyclicTotalComplex_d_apply, Iso.inv_hom_id_apply, ModuleCat.hom_ofHom]
    exact (cyclicTotalToHochschild_cyclicTotalDifferential _).symm

/-- Under the identifications of the terms of both complexes with modules of cochains, the cochain
map to the Hochschild cochain complex is the projection onto column zero. -/
@[reassoc, elementwise]
theorem cyclicTotalComplexToHochschild_f (m : ℕ) :
    (cyclicTotalComplexToHochschild R A M).f m ≫ (hochschildCochainComplexXIso R A M m).hom =
      (cyclicTotalComplexXIso R A M m).hom ≫
        ModuleCat.ofHom (cyclicTotalToHochschild R A M m) := by
  simp [cyclicTotalComplexToHochschild]

/-- Including cyclic cochains into column zero of the total complex and projecting back onto
column zero is the inclusion of the cyclic cochain complex into the Hochschild cochain complex. -/
@[reassoc (attr := simp)]
theorem cyclicCochainComplexToTotal_comp_cyclicTotalComplexToHochschild :
    cyclicCochainComplexToTotal R A M ≫ cyclicTotalComplexToHochschild R A M =
      cyclicCochainComplexι R A M := by
  refine HomologicalComplex.hom_ext _ _ fun m ↦ ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun φ ↦ ?_)
  apply (ModuleCat.mono_iff_injective (hochschildCochainComplexXIso R A M m).hom).1 inferInstance
  simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
    cyclicTotalComplexToHochschild_f_apply, cyclicCochainComplexToTotal_f_apply,
    cyclicCochainComplexι_f_apply]
  exact cyclicTotalToHochschild_cyclicCochainsToTotal _

/-- The projection onto column zero vanishes on the image of the periodicity cochain map:
`I ∘ S = 0` on cochains. -/
@[reassoc (attr := simp)]
theorem cyclicTotalComplexPeriodicity_comp_cyclicTotalComplexToHochschild :
    cyclicTotalComplexPeriodicity R A M ≫ cyclicTotalComplexToHochschild R A M = 0 := by
  refine HomologicalComplex.hom_ext _ _ fun i ↦ ?_
  match i with
  | 0 => exact (HomologicalComplex.isZero_extend_X _ (ComplexShape.embeddingUpNatAdd 2) 0
      fun _ ↦ by simp).eq_of_src _ _
  | 1 => exact (HomologicalComplex.isZero_extend_X _ (ComplexShape.embeddingUpNatAdd 2) 1
      fun _ ↦ by simp).eq_of_src _ _
  | m + 2 =>
    refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
    apply (ModuleCat.mono_iff_injective (hochschildCochainComplexXIso R A M (m + 2)).hom).1
      inferInstance
    simp only [HomologicalComplex.comp_f, ModuleCat.hom_comp, LinearMap.comp_apply,
      cyclicTotalComplexToHochschild_f_apply, cyclicTotalComplexPeriodicity_f_apply,
      HomologicalComplex.zero_f, ModuleCat.hom_zero, LinearMap.zero_apply, map_zero]
    exact cyclicTotalToHochschild_cyclicTotalPeriodicity _

/-- The periodicity map sends the class of a total cocycle `x` of degree `m` to the class of `x`,
regarded as a total cocycle of degree `m + 2`. -/
theorem cyclicTotalHomologyPeriodicity_homologyπ (m : ℕ) (x : (cyclicTotalComplex R A M).X m)
    (hx : (cyclicTotalComplex R A M).d m (m + 1) x = 0) :
    cyclicTotalHomologyPeriodicity R A M m ((cyclicTotalComplex R A M).homologyπ m
        ((cyclicTotalComplex R A M).moduleCatCyclesMk x (m + 1) (by simp) hx)) =
      (cyclicTotalComplex R A M).homologyπ (m + 2) ((cyclicTotalComplex R A M).moduleCatCyclesMk
        ((cyclicTotalComplexXIso R A M (m + 2)).inv
          (cyclicTotalPeriodicity R A M m ((cyclicTotalComplexXIso R A M m).hom x)))
        (m + 3) (by simp) (by
          apply (ModuleCat.mono_iff_injective (cyclicTotalComplexXIso R A M (m + 3)).hom).1
            inferInstance
          rw [cyclicTotalComplex_d_apply, Iso.inv_hom_id_apply,
            cyclicTotalDifferential_cyclicTotalPeriodicity, ← cyclicTotalComplex_d_apply, hx,
            map_zero, map_zero, map_zero])) := by
  rw [cyclicTotalHomologyPeriodicity, ModuleCat.comp_apply,
    HomologicalComplex.extendHomologyIso_inv_homologyπ_moduleCatCyclesMk _ _ _ _ _ _ hx (m + 3)
      (by simp) (by
        rw [HomologicalComplex.extend_d_eq _ _ (ComplexShape.embeddingUpNatAdd_f 2 m)
          (ComplexShape.embeddingUpNatAdd_f 2 (m + 1)), ModuleCat.comp_apply, ModuleCat.comp_apply,
          Iso.inv_hom_id_apply, hx, map_zero]),
    HomologicalComplex.homologyMap_homologyπ_moduleCatCyclesMk]
  congr 2
  apply (ModuleCat.mono_iff_injective (cyclicTotalComplexXIso R A M (m + 2)).hom).1 inferInstance
  rw [cyclicTotalComplexPeriodicity_f_apply, Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]

/-- The projection onto column zero sends the class of a total cocycle to the Hochschild class of
its column-zero component. -/
@[simp]
theorem homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMk {m : ℕ}
    (x : LinearMap.ker (cyclicTotalDifferential R A M m)) :
    HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) m
        (cyclicTotalHomologyMk R A M m x) =
      hochschildCohomology.mk R A M m ⟨x.1.1 m, mem_hochschildCocycles_iff.2 (by
        rw [← cyclicTotalToHochschild_apply, ← cyclicTotalToHochschild_cyclicTotalDifferential,
          LinearMap.mem_ker.1 x.2, map_zero])⟩ := by
  have hx := (mem_ker_cyclicTotalDifferential_iff R A M m x.1).1 x.2
  rw [cyclicTotalHomologyMk_eq_homologyπ x ((cyclicTotalComplex R A M).moduleCatCyclesMk _ (m + 1)
      (CochainComplex.next ℕ m) hx) (by simp),
    HomologicalComplex.homologyMap_homologyπ_moduleCatCyclesMk]
  exact (hochschildCohomology.mk_eq_homologyπ R A M _ _
    (by simp [cyclicTotalComplexToHochschild_f_apply])).symm

/-- The periodicity map sends the class of a total cocycle `x` to the class of its image under the
periodicity map. -/
@[simp]
theorem cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMk {m : ℕ}
    (x : LinearMap.ker (cyclicTotalDifferential R A M m)) :
    cyclicTotalHomologyPeriodicity R A M m (cyclicTotalHomologyMk R A M m x) =
      cyclicTotalHomologyMk R A M (m + 2) ⟨cyclicTotalPeriodicity R A M m x.1, by
        rw [LinearMap.mem_ker, cyclicTotalDifferential_cyclicTotalPeriodicity,
          LinearMap.mem_ker.1 x.2, map_zero]⟩ := by
  have hx := (mem_ker_cyclicTotalDifferential_iff R A M m x.1).1 x.2
  rw [cyclicTotalHomologyMk_eq_homologyπ x ((cyclicTotalComplex R A M).moduleCatCyclesMk _ (m + 1)
      (CochainComplex.next ℕ m) hx) (by simp),
    cyclicTotalHomologyPeriodicity_homologyπ]
  exact (cyclicTotalHomologyMk_eq_homologyπ _ _ (by simp)).symm

/-- The projection onto column zero kills the image of the periodicity map on cohomology:
`I ∘ S = 0`. -/
@[reassoc (attr := simp)]
theorem cyclicTotalHomologyPeriodicity_comp_homologyMap_cyclicTotalComplexToHochschild (m : ℕ) :
    cyclicTotalHomologyPeriodicity R A M m ≫
      HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) (m + 2) = 0 := by
  rw [cyclicTotalHomologyPeriodicity, Category.assoc, ← HomologicalComplex.homologyMap_comp,
    cyclicTotalComplexPeriodicity_comp_cyclicTotalComplexToHochschild,
    HomologicalComplex.homologyMap_zero, Limits.comp_zero]

end Complex

section Exactness

variable (R : Type*) (A : Type u) (M : Type*) [CommRing R] [Semiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- **Exactness of `H^m(Tot) → H^(m+2)(Tot) → HH^(m+2)`.** For a unital algebra, a class in the
cohomology of the total cyclic bicomplex is in the image of the periodicity map exactly when its
projection onto column zero vanishes in Hochschild cohomology. -/
theorem exact_cyclicTotalHomologyPeriodicity_homologyMap_cyclicTotalComplexToHochschild (m : ℕ) :
    Function.Exact (cyclicTotalHomologyPeriodicity R A M m)
      (HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) (m + 2)) := by
  refine fun c ↦ ⟨fun hc ↦ ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := cyclicTotalHomologyMk_surjective (m + 2) c
    rw [homologyMap_cyclicTotalComplexToHochschild_cyclicTotalHomologyMk,
      hochschildCohomology.mk_eq_zero_iff, mem_hochschildCoboundaries_succ_iff] at hc
    obtain ⟨χ, hχ⟩ := hc
    have hx : cyclicTotalDifferential R A M (m + 2) x.1 = 0 := LinearMap.mem_ker.1 x.2
    obtain ⟨w, b, hwb⟩ := exists_eq_cyclicTotalPeriodicity_add_cyclicTotalDifferential x.1 hx χ hχ
    -- `D b` lies in `cyclicTotalCochains R A M (m + 1 + 1)`, definitionally degree `m + 2`
    have hSw : cyclicTotalPeriodicity R A M m w = x.1 -
        ⟨_, (cyclicTotalDifferential R A M (m + 1) b).2⟩ :=
      Subtype.ext (by rw [Submodule.coe_sub, hwb, add_sub_cancel_right])
    have hw : cyclicTotalDifferential R A M m w = 0 := by
      apply cyclicTotalPeriodicity_injective R A M (m + 1)
      rw [← cyclicTotalDifferential_cyclicTotalPeriodicity, hSw, map_sub, hx, map_zero, zero_sub,
        neg_eq_zero]
      exact cyclicTotalDifferential_cyclicTotalDifferential b
    refine ⟨cyclicTotalHomologyMk R A M m ⟨w, hw⟩, ?_⟩
    rw [cyclicTotalHomologyPeriodicity_cyclicTotalHomologyMk, ← sub_eq_zero, ← map_sub]
    exact (cyclicTotalHomologyMk_succ_eq_zero_iff (n := m + 1) _).2
      ⟨-b, Subtype.ext (by simp [hSw])⟩
  · rintro ⟨c, rfl⟩
    rw [← ModuleCat.comp_apply,
      cyclicTotalHomologyPeriodicity_comp_homologyMap_cyclicTotalComplexToHochschild]
    rfl

end Exactness

section CyclicCohomology

variable (R : Type*) (A : Type u) (M : Type*) [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M]
  [Module R M]

/-- The map `I : HCⁿ(A; M) → HHⁿ(A, Hom_R(A, M))` on cyclic cohomology factors through the
cohomology of the total complex. -/
@[reassoc (attr := simp)]
theorem homologyMap_cyclicCochainComplexToTotal_comp_homologyMap_cyclicTotalComplexToHochschild
    (n : ℕ) :
    HomologicalComplex.homologyMap (cyclicCochainComplexToTotal R A M) n ≫
        HomologicalComplex.homologyMap (cyclicTotalComplexToHochschild R A M) n =
      cyclicCohomology.toHochschild R A M n := by
  rw [← HomologicalComplex.homologyMap_comp,
    cyclicCochainComplexToTotal_comp_cyclicTotalComplexToHochschild,
    cyclicCohomology.toHochschild_def]

end CyclicCohomology

end TauCeti
