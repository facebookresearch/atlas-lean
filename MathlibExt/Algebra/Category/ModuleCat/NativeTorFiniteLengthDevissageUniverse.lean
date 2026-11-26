/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.NativeTorEulerAdditivityUniverse
public import MathlibExt.Algebra.Category.ModuleCat.FlatHomology
public import MathlibExt.RingTheory.Length.Exact
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.SimpleModule.Basic

/-!
# Finite-length dévissage for Tor Euler sums

Let R be a commutative local ring with residue field κ, S a commutative ring, F : Mod_R →
Mod_S an additive homology-preserving functor and M an S-module. Suppose Tor_q^S(M,Fκ) has
finite S-length for q < d and vanishes for q ≥ d. Then the same finite-length and vanishing
bounds hold for Tor_q^S(M,FN) whenever N has finite R-length.

For the alternating sum χ_d(M,FN) = ∑_{q<d}(−1)^q ℓ_S(Tor_q^S(M,FN)), dévissage gives
χ_d(M,FN) = ℓ_R(N)χ_d(M,Fκ). The residue coefficient is lifted to the stated carrier universe.
Flat scalar extension R → S is a specialization of this functorial statement.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct ModuleCat.UniverseTensor ZeroObject

namespace ModuleCat.UniverseTensor

universe u v w
variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [IsLocalRing R]

/-- The lifted residue-field coefficient module.

For a commutative local ring R, this is ULift of κ = R/m as an R-module through the residue
map, at the specified carrier height. -/
def nativeResidueCoefficient : ModuleCat.{max u w} R :=
  ModuleCat.of R (ULift.{w} (IsLocalRing.ResidueField R))

/-- The residue coefficient has length one.

The lifted residue-field module has R-length 1, since the residue map is surjective and the
residue field is a simple R-module. -/
theorem nativeResidueCoefficient_length :
    Module.length R (nativeResidueCoefficient.{u, w} R) = 1 := by
  change Module.length R (ULift.{w} (IsLocalRing.ResidueField R)) = 1
  rw [(ULift.moduleEquiv : ULift.{w} (IsLocalRing.ResidueField R) ≃ₗ[R]
    IsLocalRing.ResidueField R).length_eq]
  have hsurj : Function.Surjective (algebraMap R (IsLocalRing.ResidueField R)) := by
    rw [IsLocalRing.ResidueField.algebraMap_eq]
    exact IsLocalRing.residue_surjective
  exact (Module.length_eq_of_surjective (R := IsLocalRing.ResidueField R)
    (M := IsLocalRing.ResidueField R) (S := R) hsurj).trans
      (Module.length_eq_one (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R))

private theorem simple_equiv_nativeResidueCoefficient
    (N : Type (max u w)) [AddCommGroup N] [Module R N] [IsSimpleModule R N] :
    Nonempty (N ≃ₗ[R] nativeResidueCoefficient.{u, w} R) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := (isSimpleModule_iff_quot_maximal (R := R) (M := N)).mp inferInstance
  have hi : I = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal hI
  subst I
  exact ⟨e.trans (ULift.moduleEquiv : ULift.{w} (IsLocalRing.ResidueField R) ≃ₗ[R]
    IsLocalRing.ResidueField R).symm⟩

/-- Finite lengths of outer Tor terms imply finite length of the middle term.

For a short exact sequence C₁ → C₂ → C₃ of S-modules and fixed M, if Tor_q^S(M,C₁) and
Tor_q^S(M,C₃) have finite length, so does Tor_q^S(M,C₂). -/
theorem nativeTor_length_ne_top_of_shortExact
    (M : ModuleCat.{max v w} S) (C : ShortComplex (ModuleCat.{max v w} S))
    (hC : C.ShortExact) (q : ℕ)
    (h₁ : Module.length S (((Tor (ModuleCat.{max v w} S) q).obj M).obj C.X₁) ≠ ⊤)
    (h₃ : Module.length S (((Tor (ModuleCat.{max v w} S) q).obj M).obj C.X₃) ≠ ⊤) :
    Module.length S (((Tor (ModuleCat.{max v w} S) q).obj M).obj C.X₂) ≠ ⊤ := by
  let F := (tensoringLeft (ModuleCat.{max v w} S)).obj M
  obtain ⟨_, h⟩ := LeftDerivedDelta.LDexact_B F q C hC
  exact Module.length_ne_top_of_exact S
    (((Tor (ModuleCat.{max v w} S) q).obj M).map C.f).hom
    (((Tor (ModuleCat.{max v w} S) q).obj M).map C.g).hom
    ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp h) h₁ h₃

/-- Vanishing of outer Tor terms implies vanishing of the middle term.

For a short exact coefficient sequence and fixed M, if Tor_q^S(M,C₁) and Tor_q^S(M,C₃) are
zero, then Tor_q^S(M,C₂) is zero. -/
theorem nativeTor_isZero_of_shortExact
    (M : ModuleCat.{max v w} S) (C : ShortComplex (ModuleCat.{max v w} S))
    (hC : C.ShortExact) (q : ℕ)
    (h₁ : IsZero (((Tor (ModuleCat.{max v w} S) q).obj M).obj C.X₁))
    (h₃ : IsZero (((Tor (ModuleCat.{max v w} S) q).obj M).obj C.X₃)) :
    IsZero (((Tor (ModuleCat.{max v w} S) q).obj M).obj C.X₂) := by
  let F := (tensoringLeft (ModuleCat.{max v w} S)).obj M
  obtain ⟨_, h⟩ := LeftDerivedDelta.LDexact_B F q C hC
  exact h.isZero_of_both_isZero h₁ h₃

/-- Tor Euler dévissage under a homology-preserving coefficient functor.

For additive homology-preserving F, assume Tor^S(M,Fκ) has finite length below cutoff d and is
zero at and above d. Every finite-length R-module N inherits these bounds, and its alternating
Tor length sum is ℓ_R(N) times that for Fκ. The ring and coefficient universes are as stated. -/
theorem nativeTorFiniteLength_devissage_of_preservesHomology
    (F : ModuleCat.{max u v w} R ⥤ ModuleCat.{max u v w} S)
    [F.Additive] [F.PreservesHomology] (M : ModuleCat.{max u v w} S)
    (N : Type (max u v w)) [AddCommGroup N] [Module R N] (hN : IsFiniteLength R N)
    (cutoff : ℕ)
    (hκ : ∀ q < cutoff,
      Module.length S (((@Tor (ModuleCat.{max u v w} S) inferInstance
        (monoidalCategory.{v, max u w}) inferInstance (monoidalPreadditive.{v, max u w})
        inferInstance q).obj M).obj
        (F.obj
          (nativeResidueCoefficient.{u, max v w} R))) ≠ ⊤)
    (hzκ : ∀ q, cutoff ≤ q → IsZero (((@Tor (ModuleCat.{max u v w} S) inferInstance
      (monoidalCategory.{v, max u w}) inferInstance (monoidalPreadditive.{v, max u w})
      inferInstance q).obj M).obj
      (F.obj
        (nativeResidueCoefficient.{u, max v w} R)))) :
    (∀ q < cutoff, Module.length S (((@Tor (ModuleCat.{max u v w} S) inferInstance
      (monoidalCategory.{v, max u w}) inferInstance (monoidalPreadditive.{v, max u w})
      inferInstance q).obj M).obj
      (F.obj (ModuleCat.of R N))) ≠ ⊤) ∧
    (∀ q, cutoff ≤ q → IsZero (((@Tor (ModuleCat.{max u v w} S) inferInstance
      (monoidalCategory.{v, max u w}) inferInstance (monoidalPreadditive.{v, max u w})
      inferInstance q).obj M).obj
      (F.obj (ModuleCat.of R N)))) ∧
    rawNativeTorEulerSum.{v, max u w} S M
      (F.obj (ModuleCat.of R N)) cutoff =
      ((Module.length R N).toNat : ℤ) * rawNativeTorEulerSum.{v, max u w} S M
        (F.obj
          (nativeResidueCoefficient.{u, max v w} R)) cutoff := by
  let : MonoidalCategoryStruct (ModuleCat.{max u v w} S) := tensorStructure.{v, max u w}
  let : MonoidalCategory (ModuleCat.{max u v w} S) := monoidalCategory.{v, max u w}
  let : MonoidalPreadditive (ModuleCat.{max u v w} S) := monoidalPreadditive.{v, max u w}
  let k := nativeResidueCoefficient.{u, max v w} R
  have hsimp (K : Type (max u v w)) [AddCommGroup K] [Module R K] [IsSimpleModule R K] :
      (∀ q < cutoff, Module.length S (((Tor (ModuleCat.{max u v w} S) q).obj M).obj
        (F.obj (ModuleCat.of R K))) ≠ ⊤) ∧
      (∀ q, cutoff ≤ q → IsZero (((Tor (ModuleCat.{max u v w} S) q).obj M).obj
        (F.obj (ModuleCat.of R K)))) ∧
      rawNativeTorEulerSum.{v, max u w} S M (F.obj (ModuleCat.of R K)) cutoff =
        rawNativeTorEulerSum.{v, max u w} S M (F.obj k) cutoff := by
    obtain ⟨eκ⟩ := simple_equiv_nativeResidueCoefficient.{u, max v w} R K
    let E : F.obj (ModuleCat.of R K) ≅ F.obj k := F.mapIso eκ.toModuleIso
    have eQ (q : ℕ) := ((Tor (ModuleCat.{max u v w} S) q).obj M).mapIso E
    constructor
    · intro q hq
      rw [(eQ q).toLinearEquiv.length_eq]
      exact hκ q hq
    constructor
    · intro q hq
      exact (hzκ q hq).of_iso (eQ q)
    · unfold rawNativeTorEulerSum
      apply Finset.sum_congr rfl
      intro q _
      rw [(eQ q).toLinearEquiv.length_eq]
  induction hN with
  | @of_subsingleton K _ _ _ =>
    have hz (q : ℕ) : IsZero (((Tor (ModuleCat.{max u v w} S) q).obj M).obj
        (F.obj (ModuleCat.of R K))) := by
      let T := (Tor (ModuleCat.{max u v w} S) q).obj M
      have : T.Additive := by dsimp [T, Tor]; infer_instance
      have h0 : IsZero (ModuleCat.of R K) := ModuleCat.isZero_iff_subsingleton.mpr inferInstance
      exact T.map_isZero (F.map_isZero h0)
    constructor
    · intro q _
      rw [Module.length_eq_zero_iff.mpr (ModuleCat.isZero_iff_subsingleton.mp (hz q))]
      exact ENat.zero_ne_top
    constructor
    · intro q _
      exact hz q
    · unfold rawNativeTorEulerSum
      have hlen : Module.length R K = 0 := Module.length_eq_zero
      rw [hlen]
      simp only [ENat.toNat_zero, Int.natCast_zero, zero_mul]
      apply Finset.sum_eq_zero
      intro q _
      rw [Module.length_eq_zero_iff.mpr (ModuleCat.isZero_iff_subsingleton.mp (hz q))]
      simp
  | @of_simple_quotient N _ _ p hsimple hp ih =>
    have hQ := hsimp (N ⧸ p)
    let C : ShortComplex (ModuleCat.{max u v w} R) :=
      ModuleCat.shortComplexOfCompEqZero p.subtype p.mkQ (by
        apply LinearMap.ext
        intro x
        exact (Submodule.Quotient.mk_eq_zero (p := p) (x := (x : N))).mpr x.property)
    have hC : C.ShortExact := ModuleCat.shortComplex_shortExact C
      (LinearMap.exact_subtype_mkQ p) p.injective_subtype p.mkQ_surjective
    have : F.PreservesMonomorphisms := Functor.preservesMonomorphisms_of_map_exact F
      (fun D hD => hD.map F)
    have : F.PreservesEpimorphisms := Functor.preservesEpimorphisms_of_map_exact F
      (fun D hD => hD.map F)
    have : Mono C.f := hC.mono_f
    have : Epi C.g := hC.epi_g
    have hCF : (C.map F).ShortExact := hC.map F
    have hfinite : ∀ q < cutoff, Module.length S
        (((Tor (ModuleCat.{max u v w} S) q).obj M).obj (F.obj (ModuleCat.of R N))) ≠ ⊤ := by
      intro q hq
      exact nativeTor_length_ne_top_of_shortExact.{v, max u w} S M (C.map F) hCF q
        (ih.1 q hq) (hQ.1 q hq)
    have hzero : ∀ q, cutoff ≤ q → IsZero
        (((Tor (ModuleCat.{max u v w} S) q).obj M).obj (F.obj (ModuleCat.of R N))) := by
      intro q hq
      exact nativeTor_isZero_of_shortExact.{v, max u w} S M (C.map F) hCF q
        (ih.2.1 q hq) (hQ.2.1 q hq)
    refine ⟨hfinite, hzero, ?_⟩
    have he := rawNativeTorEulerSum_shortExactSecond.{v, max u w} S M (C.map F) hCF cutoff
      ih.1 hfinite hQ.1 (hQ.2.1 cutoff le_rfl)
    have hlen : Module.length R N = Module.length R p + 1 := by
      rw [Module.length_eq_add_of_exact p.subtype p.mkQ p.injective_subtype
        p.mkQ_surjective (LinearMap.exact_subtype_mkQ p), Module.length_eq_one R (N ⧸ p)]
    have hpfin : Module.length R p ≠ ⊤ := Module.length_ne_top_iff.mpr hp
    have hnat : ((Module.length R N).toNat : ℤ) = ((Module.length R p).toNat : ℤ) + 1 := by
      rw [hlen, ENat.toNat_add hpfin ENat.one_ne_top]
      simp
    change rawNativeTorEulerSum.{v, max u w} S M (F.obj (ModuleCat.of R N)) cutoff =
      rawNativeTorEulerSum.{v, max u w} S M (F.obj (ModuleCat.of R p)) cutoff +
        rawNativeTorEulerSum.{v, max u w} S M (F.obj (ModuleCat.of R (N ⧸ p))) cutoff at he
    change rawNativeTorEulerSum.{v, max u w} S M (F.obj (ModuleCat.of R N)) cutoff =
      ((Module.length R N).toNat : ℤ) * rawNativeTorEulerSum.{v, max u w} S M (F.obj k) cutoff
    rw [he, ih.2.2, hQ.2.2, hnat]
    ring

variable [Algebra R S] [Module.Flat R S]

/-- Tor Euler dévissage after flat scalar extension.

For a flat R-algebra S and finite-length R-module N, finite-length and vanishing bounds for
Tor^S(M,S⊗_R κ) pass to Tor^S(M,S⊗_R N). Its alternating sum below the common cutoff is ℓ_R(N)
times the residue-coefficient sum. -/
theorem nativeTorFiniteLength_devissage (M : ModuleCat.{max u v w} S)
    (N : Type (max u v w)) [AddCommGroup N] [Module R N] (hN : IsFiniteLength R N)
    (cutoff : ℕ)
    (hκ : ∀ q < cutoff,
      Module.length S (((@Tor (ModuleCat.{max u v w} S) inferInstance
        (monoidalCategory.{v, max u w}) inferInstance (monoidalPreadditive.{v, max u w})
        inferInstance q).obj M).obj
        ((extendScalars.{u, v, max u v w} (algebraMap R S)).obj
          (nativeResidueCoefficient.{u, max v w} R))) ≠ ⊤)
    (hzκ : ∀ q, cutoff ≤ q → IsZero (((@Tor (ModuleCat.{max u v w} S) inferInstance
      (monoidalCategory.{v, max u w}) inferInstance (monoidalPreadditive.{v, max u w})
      inferInstance q).obj M).obj
      ((extendScalars.{u, v, max u v w} (algebraMap R S)).obj
        (nativeResidueCoefficient.{u, max v w} R)))) :
    (∀ q < cutoff, Module.length S (((@Tor (ModuleCat.{max u v w} S) inferInstance
      (monoidalCategory.{v, max u w}) inferInstance (monoidalPreadditive.{v, max u w})
      inferInstance q).obj M).obj
      ((extendScalars.{u, v, max u v w} (algebraMap R S)).obj (ModuleCat.of R N))) ≠ ⊤) ∧
    (∀ q, cutoff ≤ q → IsZero (((@Tor (ModuleCat.{max u v w} S) inferInstance
      (monoidalCategory.{v, max u w}) inferInstance (monoidalPreadditive.{v, max u w})
      inferInstance q).obj M).obj
      ((extendScalars.{u, v, max u v w} (algebraMap R S)).obj (ModuleCat.of R N)))) ∧
    rawNativeTorEulerSum.{v, max u w} S M
      ((extendScalars.{u, v, max u v w} (algebraMap R S)).obj (ModuleCat.of R N)) cutoff =
      ((Module.length R N).toNat : ℤ) * rawNativeTorEulerSum.{v, max u w} S M
        ((extendScalars.{u, v, max u v w} (algebraMap R S)).obj
          (nativeResidueCoefficient.{u, max v w} R)) cutoff := by
  let F : ModuleCat.{max u v w} R ⥤ ModuleCat.{max u v w} S :=
    extendScalars.{u, v, max u v w} (algebraMap R S)
  have : F.PreservesHomology := preservesHomology_extendScalars_of_flat.{u, v, w}
    (algebraMap R S) (by rw [RingHom.flat_algebraMap_iff]; infer_instance)
  exact nativeTorFiniteLength_devissage_of_preservesHomology.{u, v, w}
    R S F M N hN cutoff hκ hzκ

end ModuleCat.UniverseTensor
