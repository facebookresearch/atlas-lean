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
TauCeti/RingTheory/CyclicCohomology/Hochschild.lean
Public source: https://github.com/TauCetiProject/TauCeti
The original contributors' copyright, author and Apache License 2.0
notice is retained above. Modification notice: use the explicitly
listed MathlibExt ports for this complete SBI dependency closure;
retain the mathematical declarations and original names. Identity-scalar
multilinear maps and endomorphism-application lemmas use the pinned
Mathlib API; the finite-coordinate port keeps only its four needed lemmas.
-/
module

public import MathlibExt.RingTheory.CyclicCohomology
public import MathlibExt.RingTheory.ConnesOperator
public import MathlibExt.RingTheory.HochschildCochains
import MathlibExt.Algebra.Homology.CyclicModuleHomology

/-!
# The maps `I` and `B` of the SBI sequence

Connes' cyclic cochain complex is a subcomplex of the Hochschild cochain complex
`hochschildCochainComplex R A M` of `TauCeti.RingTheory.HochschildCohomology.Complex`, whose
cohomology is the Hochschild cohomology `HHⁿ(A, Hom_R(A, M))`. The inclusion
`cyclicCochainComplexι R A M` induces `I : HCⁿ(A; M) → HHⁿ(A, Hom_R(A, M))`
(`cyclicCohomology.toHochschild`). In the other direction, Connes' operator
`B : Cⁿ⁺¹ → Cⁿ` takes values in cyclic cochains and anticommutes with `b`, so it sends Hochschild
cocycles to cyclic cocycles and Hochschild coboundaries to cyclic coboundaries; it therefore
induces `B : HHⁿ⁺¹(A, Hom_R(A, M)) → HCⁿ(A; M)` (`hochschildCohomology.connesB`). Since `B`
vanishes on cyclic cochains, the composite `B ∘ I : HCⁿ⁺¹ → HHⁿ⁺¹ → HCⁿ` is zero. When `R`
contains `ℚ`, these are the maps `I` and `B` of Connes' long exact sequence
`⋯ → HCⁿ → HHⁿ → HCⁿ⁻¹ → HCⁿ⁺¹ → HHⁿ⁺¹ → ⋯`,
whose remaining map is the periodicity operator `S`. Over a general ground ring the cohomology of
the cyclic cochains need not fit into such an exact sequence; the maps `I` and `B` and the
identity `B ∘ I = 0` are nevertheless constructed here for every commutative ring `R`.
The cocycle and coboundary lemmas also apply to semiring scalars whose action on `M` commutes
with itself.

In degree zero there are no coboundaries, every cochain is cyclic and the cocycles are the traces,
so `I : HC⁰(A; M) → HH⁰(A, Hom_R(A, M))` is an isomorphism. In degree one, a cyclic cocycle which
is a Hochschild coboundary `b ψ` is the cyclic coboundary of the cyclic `0`-cochain `ψ`, so
`I : HC¹(A; M) → HH¹(A, Hom_R(A, M))` is injective, over every commutative ring `R`.

## Main definitions

* `TauCeti.cyclicCochainComplexι`: the inclusion of the cyclic cochain complex.
* `TauCeti.cyclicCohomology.toHochschild`: the map `I : HCⁿ(A; M) → HHⁿ(A, Hom_R(A, M))`.
* `TauCeti.hochschildCohomology.connesB`: the map `B : HHⁿ⁺¹(A, Hom_R(A, M)) → HCⁿ(A; M)`.

## Main results

* `TauCeti.cyclicCohomology.toHochschild_mk`, `TauCeti.hochschildCohomology.connesB_mk`: `I` and
  `B` on representing cocycles.
* `TauCeti.cyclicCohomology.toHochschild_comp_connesB`: `B ∘ I = 0`.
* `TauCeti.cyclicCohomology.isIso_toHochschild_zero`: `I` is an isomorphism in degree zero.
* `TauCeti.cyclicCohomology.injective_toHochschild_one`: `I` is injective in degree one.

## References

* A. Connes, *Noncommutative Geometry*, Chapter III, §1.
* J.-L. Loday, *Cyclic Homology*, §2.4.
-/

public section

noncomputable section

open CategoryTheory

namespace TauCeti

universe u

section Cocycles

variable {R : Type*} {A : Type u} {M : Type*} [Semiring R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M]

/-- A cyclic cocycle is a Hochschild cocycle. -/
theorem mem_hochschildCocycles_of_mem_cyclicCocycles {n : ℕ} {φ : cyclicCochains R A M n}
    (hφ : φ ∈ cyclicCocycles R A M n) :
    (φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 1) ↦ A) M) ∈ hochschildCocycles R A M n :=
  mem_hochschildCocycles_iff.2 ((mem_cyclicCocycles_iff R A M).1 hφ)

end Cocycles

section Complex

variable (R : Type*) (A : Type u) (M : Type*) [CommRing R] [NonUnitalSemiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]

/-- The inclusion of Connes' cyclic cochain complex into the Hochschild cochain complex. -/
def cyclicCochainComplexι : cyclicCochainComplex R A M ⟶ hochschildCochainComplex R A M where
  f n := (cyclicCochainComplexXIso R A M n).hom ≫
    ModuleCat.ofHom (cyclicCochains R A M n).subtype ≫ (hochschildCochainComplexXIso R A M n).inv
  comm' := by
    rintro n _ rfl
    refine ModuleCat.hom_ext (LinearMap.ext fun φ ↦ ?_)
    apply (ModuleCat.mono_iff_injective (hochschildCochainComplexXIso R A M (n + 1)).hom).1
      inferInstance
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, hochschildCochainComplex_d_apply,
      Iso.inv_hom_id_apply, cyclicCochainComplex_d_apply, ModuleCat.hom_ofHom,
      Submodule.subtype_apply]
    exact (coe_cyclicHochschildCoboundary_apply R A M _).symm

/-- Under the identifications of the terms of both complexes with modules of cochains, the
inclusion of the cyclic cochain complex is the inclusion of the cyclic cochains. -/
@[reassoc, elementwise]
theorem cyclicCochainComplexι_f (n : ℕ) :
    (cyclicCochainComplexι R A M).f n ≫ (hochschildCochainComplexXIso R A M n).hom =
      (cyclicCochainComplexXIso R A M n).hom ≫
        ModuleCat.ofHom (cyclicCochains R A M n).subtype := by
  simp [cyclicCochainComplexι]

end Complex

section ConnesB

variable {R : Type*} {A : Type u} {M : Type*} [Semiring R] [Semiring A] [Module R A]
  [IsScalarTower R A A] [SMulCommClass R A A] [AddCommGroup M] [Module R M]
  [SMulCommClass R R M]

/-- Connes' operator `B` sends a Hochschild `(n + 1)`-cocycle to a cyclic `n`-cocycle. -/
theorem connesB_mem_cyclicCocycles {n : ℕ} {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2)
    ↦ A) M}
    (hφ : φ ∈ hochschildCocycles R A M (n + 1)) :
    (⟨connesB R A M n φ, connesB_mem_cyclicCochains φ⟩ : cyclicCochains R A M n) ∈
      cyclicCocycles R A M n := by
  have h := hochschildCoboundary_connesB_add_connesB_hochschildCoboundary φ
  rw [mem_hochschildCocycles_iff.1 hφ, map_zero, add_zero] at h
  exact (mem_cyclicCocycles_iff R A M).2 h

/-- Connes' operator `B` sends a Hochschild `(n + 1)`-coboundary to a cyclic `n`-coboundary. -/
theorem connesB_mem_cyclicCoboundaries {n : ℕ}
    {φ : MultilinearMap (RingHom.id R) (fun _ : Fin (n + 2) ↦ A) M}
    (hφ : φ ∈ hochschildCoboundaries R A M (n + 1)) :
    (⟨connesB R A M n φ, connesB_mem_cyclicCochains φ⟩ : cyclicCochains R A M n) ∈
      cyclicCoboundaries R A M n := by
  obtain ⟨ψ, rfl⟩ := mem_hochschildCoboundaries_succ_iff.1 hφ
  cases n with
  | zero =>
    -- `B (b ψ) = 0` in degree zero (`connesB_hochschildCoboundary_zero`).
    simp
  | succ n =>
    -- Use `B (-ψ)` as the cyclic primitive; this avoids needing negation on the submodule.
    refine (mem_cyclicCoboundaries_succ_iff R A M).2
      ⟨⟨connesB R A M n (-ψ), connesB_mem_cyclicCochains _⟩, Subtype.ext ?_⟩
    simpa only [coe_cyclicHochschildCoboundary_apply, Subtype.coe_mk, map_neg,
      neg_eq_iff_add_eq_zero] using
      hochschildCoboundary_connesB_add_connesB_hochschildCoboundary ψ

end ConnesB

section Cohomology

variable (R : Type*) (A : Type u) (M : Type*) [CommRing R] [Ring A] [Algebra R A] [AddCommGroup M]
  [Module R M]

namespace hochschildCohomology

/-- Connes' operator `B`, from Hochschild `(n + 1)`-cocycles to cyclic `n`-cocycles. -/
private def connesBCocycles (n : ℕ) :
    hochschildCocycles R A M (n + 1) →ₗ[R] cyclicCocycles R A M n :=
  LinearMap.codRestrict _
    (LinearMap.codRestrict _ (TauCeti.connesB R A M n) connesB_mem_cyclicCochains ∘ₗ
      (hochschildCocycles R A M (n + 1)).subtype)
    fun φ ↦ connesB_mem_cyclicCocycles φ.2

/-- The map `B : HHⁿ⁺¹(A, Hom_R(A, M)) → HCⁿ(A; M)` induced by Connes' operator `B`; when `R`
contains `ℚ` it is the map `B` of the SBI sequence. -/
def connesB (n : ℕ) : hochschildCohomology R A M (n + 1) ⟶ cyclicCohomology R A M n :=
  ModuleCat.ofHom (X := hochschildCohomology R A M (n + 1)) (Y := cyclicCohomology R A M n) <|
    desc (n + 1) (cyclicCohomology.mk R A M n ∘ₗ connesBCocycles R A M n) fun _ hφ ↦
      (cyclicCohomology.mk_eq_zero_iff R A M n _).2 (connesB_mem_cyclicCoboundaries hφ)

/-- The map `B` sends the class of a Hochschild cocycle `φ` to the cyclic class of `B φ`. -/
@[simp]
theorem connesB_mk {n : ℕ} (φ : hochschildCocycles R A M (n + 1)) :
    connesB R A M n (mk R A M (n + 1) φ) =
      cyclicCohomology.mk R A M n
        ⟨⟨TauCeti.connesB R A M n φ, connesB_mem_cyclicCochains _⟩,
          connesB_mem_cyclicCocycles φ.2⟩ :=
  desc_mk _ _ _ φ

end hochschildCohomology

namespace cyclicCohomology

/-- The map `I : HCⁿ(A; M) → HHⁿ(A, Hom_R(A, M))` induced by the inclusion of the cyclic cochain
complex into the Hochschild cochain complex; when `R` contains `ℚ` it is the map `I` of the SBI
sequence. -/
def toHochschild (n : ℕ) : cyclicCohomology R A M n ⟶ hochschildCohomology R A M n :=
  HomologicalComplex.homologyMap (cyclicCochainComplexι R A M) n

/-- The map `I` is the map induced on cohomology by the inclusion of the cyclic cochain complex
into the Hochschild cochain complex. -/
theorem toHochschild_def (n : ℕ) :
    toHochschild R A M n = HomologicalComplex.homologyMap (cyclicCochainComplexι R A M) n :=
  (rfl)

/-- The map `I` sends the class of a cyclic cocycle to the Hochschild class of the same
cochain. -/
@[simp]
theorem toHochschild_mk {n : ℕ} (φ : cyclicCocycles R A M n) :
    toHochschild R A M n (mk R A M n φ) =
      hochschildCohomology.mk R A M n
        ⟨φ, mem_hochschildCocycles_of_mem_cyclicCocycles φ.2⟩ := by
  have hφ := (mem_cyclicCocycles_iff_complex R A M n φ.1).1 φ.2
  rw [toHochschild, mk_eq_homologyπ R A M φ
    ((cyclicCochainComplex R A M).moduleCatCyclesMk _ (n + 1) (CochainComplex.next ℕ n) hφ)
    (by rw [HomologicalComplex.iCycles_moduleCatCyclesMk, Iso.inv_hom_id_apply])]
  refine (HomologicalComplex.homologyMap_homologyπ_moduleCatCyclesMk _ _ _ _ hφ).trans
    (hochschildCohomology.mk_eq_homologyπ R A M _ _ ?_).symm
  rw [HomologicalComplex.iCycles_moduleCatCyclesMk, cyclicCochainComplexι_f_apply,
    Iso.inv_hom_id_apply]

/-- The composite `B ∘ I : HCⁿ⁺¹(A; M) → HHⁿ⁺¹(A, Hom_R(A, M)) → HCⁿ(A; M)` vanishes, since Connes'
operator `B` vanishes on cyclic cochains. This holds over every commutative ring `R`. -/
@[reassoc (attr := simp)]
theorem toHochschild_comp_connesB (n : ℕ) :
    toHochschild R A M (n + 1) ≫ hochschildCohomology.connesB R A M n = 0 := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x ↦ ?_)
  obtain ⟨φ, rfl⟩ := mk_surjective R A M (n + 1) x
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, toHochschild_mk, hochschildCohomology.connesB_mk,
    ModuleCat.hom_zero, LinearMap.zero_apply, mk_eq_zero_iff]
  convert Submodule.zero_mem _
  ext1
  exact connesB_eq_zero_of_mem_cyclicCochains φ.1.2

/-- In degree zero the map `I : HC⁰(A; M) → HH⁰(A, Hom_R(A, M))` is an isomorphism: every
`0`-cochain is cyclic and there are no coboundaries in degree zero. -/
instance isIso_toHochschild_zero : IsIso (toHochschild R A M 0) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨fun x y hxy ↦ ?_, fun x ↦ ?_⟩
  · obtain ⟨φ, rfl⟩ := mk_surjective R A M 0 x
    obtain ⟨ψ, rfl⟩ := mk_surjective R A M 0 y
    rw [toHochschild_mk, toHochschild_mk, hochschildCohomology.mk_eq_mk_iff,
      hochschildCoboundaries_zero, Submodule.mem_bot, sub_eq_zero] at hxy
    rw [mk_eq_mk_iff, cyclicCoboundaries_zero, Submodule.mem_bot, sub_eq_zero]
    exact Subtype.ext hxy
  · obtain ⟨φ, rfl⟩ := hochschildCohomology.mk_surjective R A M 0 x
    have hφ : φ.1 ∈ cyclicCochains R A M 0 := by simp
    refine ⟨mk R A M 0
      ⟨⟨φ, hφ⟩, (mem_cyclicCocycles_iff R A M).2 (mem_hochschildCocycles_iff.1 φ.2)⟩, ?_⟩
    rw [toHochschild_mk]

/-- The map `I : HC¹(A; M) → HH¹(A, Hom_R(A, M))` is injective: a cyclic `1`-cocycle which is the
Hochschild coboundary of a `0`-cochain `ψ` is the cyclic coboundary of `ψ`, since every `0`-cochain
is cyclic. This is the exactness of the SBI sequence at `HC¹`. -/
theorem injective_toHochschild_one : Function.Injective (toHochschild R A M 1) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
  obtain ⟨φ, rfl⟩ := mk_surjective R A M 1 x
  rw [toHochschild_mk, hochschildCohomology.mk_eq_zero_iff,
    mem_hochschildCoboundaries_succ_iff] at hx
  obtain ⟨ψ, hψ⟩ := hx
  have hψ' : ψ ∈ cyclicCochains R A M 0 := by simp
  rw [mk_eq_zero_iff, mem_cyclicCoboundaries_succ_iff]
  exact ⟨⟨ψ, hψ'⟩, Subtype.ext (by rw [coe_cyclicHochschildCoboundary_apply, hψ])⟩

end cyclicCohomology

end Cohomology

end TauCeti
