/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Lie.Semisimple.Defs

import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.Algebra.Lie.Abelian
import Mathlib.Algebra.Lie.AdjointAction.Derivation
import Mathlib.Algebra.Lie.CartanCriterion
import Mathlib.Algebra.Lie.Engel
import Mathlib.Algebra.Lie.LieTheorem
import Mathlib.Algebra.Lie.Nilpotent
import Mathlib.Algebra.Lie.Prod
import Mathlib.Algebra.Lie.SemiDirect
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.Sort
import Mathlib.Data.Set.Finite.List
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Prod
import Mathlib.LinearAlgebra.Projection
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.RingTheory.TwoSidedIdeal.Operations
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NoncommRing

import MathlibExt.Algebra.Lie.LeviDecomposition

attribute [local instance 100] LieRing.ofAssociativeRing

@[expose] public section

/-!
# Ado's theorem

This file proves Ado's theorem over fields of characteristic zero. It builds finite-dimensional
representations from quotients of universal enveloping algebras, then uses the Levi decomposition.
-/

namespace MathlibExt.Algebra.Lie.LandmarkWanted

private theorem ado_transport_fin
    {K L V : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    (ρ : L →ₗ⁅K⁆ Module.End K V) (hρ : Function.Injective ρ) :
    ∃ (n : ℕ) (ρ' : L →ₗ⁅K⁆ Module.End K (Fin n → K)),
      Function.Injective ρ' := by
  let _ : Module.Free K V := Module.Free.of_divisionRing K V
  let e := (Module.finBasis K V).equivFun
  refine ⟨Module.finrank K V, e.lieConj.comp ρ, ?_⟩
  exact e.lieConj.injective.comp hρ

private def adoDirectSum
    {K L V W : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (ρ : L →ₗ⁅K⁆ Module.End K V) (σ : L →ₗ⁅K⁆ Module.End K W) :
    L →ₗ⁅K⁆ Module.End K (V × W) :=
  (LinearMap.prodMapAlgHom K V W).toLieHom.comp (ρ.prod σ)

private theorem adoDirectSum_eq_zero_iff
    {K L V W : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (ρ : L →ₗ⁅K⁆ Module.End K V) (σ : L →ₗ⁅K⁆ Module.End K W) (x : L) :
    adoDirectSum ρ σ x = 0 ↔ ρ x = 0 ∧ σ x = 0 := by
  constructor
  · intro h
    constructor
    · ext v
      exact congrArg Prod.fst (LinearMap.congr_fun h (v, 0))
    · ext w
      exact congrArg Prod.snd (LinearMap.congr_fun h (0, w))
  · rintro ⟨hρ, hσ⟩
    change (ρ x).prodMap (σ x) = 0
    rw [hρ, hσ]
    exact LinearMap.prodMap_zero

private def adoAbelianShearLinear
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] :
    L →ₗ[K] Module.End K (L × K) where
  toFun x :=
    { toFun := fun p => (p.2 • x, 0)
      map_add' := by
        intro p q
        ext <;> simp [add_smul]
      map_smul' := by
        intro c p
        ext <;> simp [mul_smul] }
  map_add' x y := by
    ext p <;> simp [smul_add]
  map_smul' c x := by
    ext p <;> simp [smul_smul, mul_comm]

private def adoAbelianShear
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [IsLieAbelian L] :
    L →ₗ⁅K⁆ Module.End K (L × K) where
  toLinearMap := adoAbelianShearLinear
  map_lie' := by
    intro x y
    rw [trivial_lie_zero L L]
    ext p <;> simp [adoAbelianShearLinear, Module.End.lie_apply]

private theorem adoAbelianShear_injective
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [IsLieAbelian L] :
    Function.Injective (adoAbelianShear (K := K) (L := L)) := by
  intro x y h
  have hxy := LinearMap.congr_fun h (0, 1)
  simpa [adoAbelianShear, adoAbelianShearLinear] using congrArg Prod.fst hxy

private theorem adoAbelianShear_mul_eq_zero
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [IsLieAbelian L]
    (x y : L) :
    adoAbelianShear (K := K) x * adoAbelianShear (K := K) y = 0 := by
  ext p <;> simp [adoAbelianShear, adoAbelianShearLinear, Module.End.mul_apply]

private theorem ado_faithful_of_faithful_on_center
    {K L V : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup V] [Module K V]
    (ρ : L →ₗ⁅K⁆ Module.End K V)
    (hρ : ∀ x : L, x ∈ LieAlgebra.center K L → ρ x = 0 → x = 0) :
    Function.Injective (adoDirectSum ρ (LieModule.toEnd K L L)) := by
  intro x y hxy
  have hzero : adoDirectSum ρ (LieModule.toEnd K L L) (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨hρzero, hadzero⟩ :=
    (adoDirectSum_eq_zero_iff ρ (LieModule.toEnd K L L) (x - y)).mp hzero
  have hcenter : x - y ∈ LieAlgebra.center K L := by
    rw [← LieAlgebra.self_module_ker_eq_center K L]
    rw [LieModule.mem_ker]
    intro z
    have hz := LinearMap.congr_fun hadzero z
    simpa only [LieModule.toEnd_apply_apply, LinearMap.zero_apply] using hz
  exact sub_eq_zero.mp (hρ (x - y) hcenter hρzero)

private def adoLieDerivationToSquareZero
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    (D : LieDerivation K L L) :
    L →ₗ⁅K⁆ TrivSqZeroExt (UniversalEnvelopingAlgebra K L)
      (UniversalEnvelopingAlgebra K L) where
  toLinearMap := (UniversalEnvelopingAlgebra.ι K).toLinearMap.prod
    ((UniversalEnvelopingAlgebra.ι K).toLinearMap.comp D.toLinearMap)
  map_lie' := by
    intro x y
    apply TrivSqZeroExt.ext
    · exact LieHom.map_lie (UniversalEnvelopingAlgebra.ι K) x y
    · change UniversalEnvelopingAlgebra.ι K (D ⁅x, y⁆) =
        (UniversalEnvelopingAlgebra.ι K x * UniversalEnvelopingAlgebra.ι K (D y) +
          UniversalEnvelopingAlgebra.ι K (D x) * UniversalEnvelopingAlgebra.ι K y) -
        (UniversalEnvelopingAlgebra.ι K y * UniversalEnvelopingAlgebra.ι K (D x) +
          UniversalEnvelopingAlgebra.ι K (D y) * UniversalEnvelopingAlgebra.ι K x)
      rw [D.apply_lie_eq_add, map_add, LieHom.map_lie, LieHom.map_lie]
      simp only [Ring.lie_def]
      noncomm_ring

private def adoUniversalLift
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    (D : LieDerivation K L L) :
    UniversalEnvelopingAlgebra K L →ₐ[K]
      TrivSqZeroExt (UniversalEnvelopingAlgebra K L)
        (UniversalEnvelopingAlgebra K L) :=
  UniversalEnvelopingAlgebra.lift K (adoLieDerivationToSquareZero D)

private theorem adoUniversalLift_fst
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    (D : LieDerivation K L L) (u : UniversalEnvelopingAlgebra K L) :
    (adoUniversalLift D u).fst = u := by
  let f := (TrivSqZeroExt.fstHom K (UniversalEnvelopingAlgebra K L)
    (UniversalEnvelopingAlgebra K L)).comp (adoUniversalLift D)
  have hf : f = AlgHom.id K (UniversalEnvelopingAlgebra K L) := by
    apply UniversalEnvelopingAlgebra.hom_ext K
    ext x
    change (adoUniversalLift D (UniversalEnvelopingAlgebra.ι K x)).fst =
      UniversalEnvelopingAlgebra.ι K x
    rw [adoUniversalLift, UniversalEnvelopingAlgebra.lift_ι_apply]
    rfl
  exact DFunLike.congr_fun hf u

private def adoExtendDerivation
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    (D : LieDerivation K L L) :
    UniversalEnvelopingAlgebra K L →ₗ[K] UniversalEnvelopingAlgebra K L :=
  (LinearMap.snd K (UniversalEnvelopingAlgebra K L)
    (UniversalEnvelopingAlgebra K L)).comp (adoUniversalLift D).toLinearMap

private theorem adoExtendDerivation_ι
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    (D : LieDerivation K L L) (x : L) :
    adoExtendDerivation D (UniversalEnvelopingAlgebra.ι K x) =
      UniversalEnvelopingAlgebra.ι K (D x) := by
  change (adoUniversalLift D (UniversalEnvelopingAlgebra.ι K x)).snd = _
  rw [adoUniversalLift, UniversalEnvelopingAlgebra.lift_ι_apply]
  rfl

private theorem adoExtendDerivation_mul
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    (D : LieDerivation K L L) (u v : UniversalEnvelopingAlgebra K L) :
    adoExtendDerivation D (u * v) =
      u * adoExtendDerivation D v + adoExtendDerivation D u * v := by
  change (adoUniversalLift D (u * v)).snd = _
  rw [map_mul, TrivSqZeroExt.snd_mul, adoUniversalLift_fst,
    adoUniversalLift_fst]
  rfl

private def adoDerivationToSquareZero
    {K A : Type*} [Field K] [Ring A] [Algebra K A]
    (d : A →ₗ[K] A) (hd : ∀ u v, d (u * v) = u * d v + d u * v) :
    A →ₐ[K] TrivSqZeroExt A A := by
  have hd1 : d 1 = 0 := by
    have h := hd 1 1
    simp only [one_mul, mul_one] at h
    have h' := congrArg (fun z => z - d 1) h
    simpa using h'.symm
  exact
    { toFun := fun u => (u, d u)
      map_one' := by
        apply TrivSqZeroExt.ext
        · rfl
        · exact hd1
      map_mul' := by
        intro u v
        apply TrivSqZeroExt.ext
        · rfl
        · exact hd u v
      map_zero' := by
        apply TrivSqZeroExt.ext <;> simp
      map_add' := by
        intro u v
        apply TrivSqZeroExt.ext
        · rfl
        · exact d.map_add u v
      commutes' := by
        intro c
        rw [TrivSqZeroExt.algebraMap_eq_inl']
        apply TrivSqZeroExt.ext
        · rfl
        · simpa [Algebra.smul_def, hd1] using d.map_smul c 1 }

private theorem ado_derivation_ext
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    (d e : UniversalEnvelopingAlgebra K L →ₗ[K] UniversalEnvelopingAlgebra K L)
    (hd : ∀ u v, d (u * v) = u * d v + d u * v)
    (he : ∀ u v, e (u * v) = u * e v + e u * v)
    (hι : ∀ x, d (UniversalEnvelopingAlgebra.ι K x) =
      e (UniversalEnvelopingAlgebra.ι K x)) : d = e := by
  let fd := adoDerivationToSquareZero d hd
  let fe := adoDerivationToSquareZero e he
  have hfe : fd = fe := by
    apply UniversalEnvelopingAlgebra.hom_ext K
    ext x
    · rfl
    · exact hι x
  apply LinearMap.ext
  intro u
  exact congrArg TrivSqZeroExt.snd (DFunLike.congr_fun hfe u)

private theorem adoExtendDerivation_add
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    (D E : LieDerivation K L L) :
    adoExtendDerivation (D + E) = adoExtendDerivation D + adoExtendDerivation E := by
  apply ado_derivation_ext
  · exact adoExtendDerivation_mul (D + E)
  · intro u v
    simp only [LinearMap.add_apply, adoExtendDerivation_mul]
    noncomm_ring
  · intro x
    change adoExtendDerivation (D + E) (UniversalEnvelopingAlgebra.ι K x) =
      adoExtendDerivation D (UniversalEnvelopingAlgebra.ι K x) +
        adoExtendDerivation E (UniversalEnvelopingAlgebra.ι K x)
    rw [adoExtendDerivation_ι, adoExtendDerivation_ι, adoExtendDerivation_ι]
    simp

private theorem adoExtendDerivation_smul
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    (c : K) (D : LieDerivation K L L) :
    adoExtendDerivation (c • D) = c • adoExtendDerivation D := by
  apply ado_derivation_ext
  · exact adoExtendDerivation_mul (c • D)
  · intro u v
    simp only [LinearMap.smul_apply, adoExtendDerivation_mul, smul_add,
      mul_smul_comm, smul_mul_assoc]
  · intro x
    change adoExtendDerivation (c • D) (UniversalEnvelopingAlgebra.ι K x) =
      c • adoExtendDerivation D (UniversalEnvelopingAlgebra.ι K x)
    rw [adoExtendDerivation_ι, adoExtendDerivation_ι]
    simp

private theorem adoExtendDerivation_lie
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    (D E : LieDerivation K L L) :
    adoExtendDerivation ⁅D, E⁆ = ⁅adoExtendDerivation D, adoExtendDerivation E⁆ := by
  apply ado_derivation_ext
  · exact adoExtendDerivation_mul ⁅D, E⁆
  · intro u v
    change adoExtendDerivation D (adoExtendDerivation E (u * v)) -
        adoExtendDerivation E (adoExtendDerivation D (u * v)) =
      u * (adoExtendDerivation D (adoExtendDerivation E v) -
        adoExtendDerivation E (adoExtendDerivation D v)) +
      (adoExtendDerivation D (adoExtendDerivation E u) -
        adoExtendDerivation E (adoExtendDerivation D u)) * v
    simp only [adoExtendDerivation_mul, map_add]
    noncomm_ring
  · intro x
    change adoExtendDerivation ⁅D, E⁆ (UniversalEnvelopingAlgebra.ι K x) =
      adoExtendDerivation D
          (adoExtendDerivation E (UniversalEnvelopingAlgebra.ι K x)) -
        adoExtendDerivation E
          (adoExtendDerivation D (UniversalEnvelopingAlgebra.ι K x))
    rw [adoExtendDerivation_ι, adoExtendDerivation_ι, adoExtendDerivation_ι,
      adoExtendDerivation_ι, adoExtendDerivation_ι, LieDerivation.lie_apply, map_sub]

private def adoExtendDerivationHom
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] :
    LieDerivation K L L →ₗ⁅K⁆
      Module.End K (UniversalEnvelopingAlgebra K L) where
  toLinearMap :=
    { toFun := adoExtendDerivation
      map_add' := adoExtendDerivation_add
      map_smul' := adoExtendDerivation_smul }
  map_lie' := fun {D E} => adoExtendDerivation_lie D E

private def adoIdealAd
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    (I : LieIdeal K L) : L →ₗ⁅K⁆ LieDerivation K I I where
  toLinearMap :=
    { toFun := fun x =>
        { toLinearMap := LieModule.toEnd K L I x
          leibniz' := by
            intro y z
            apply Subtype.ext
            change ⁅x, ⁅y.1, z.1⁆⁆ = ⁅y.1, ⁅x, z.1⁆⁆ - ⁅z.1, ⁅x, y.1⁆⁆
            rw [sub_eq_add_neg, ← lie_skew z.1 ⁅x, y.1⁆, lie_lie x y.1 z.1]
            abel }
      map_add' := by
        intro x y
        ext z
        simp
      map_smul' := by
        intro c x
        ext z
        simp }
  map_lie' := by
    intro x y
    ext z
    exact lie_lie x y z.1

private def adoLeftRegularLie
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] :
    L →ₗ⁅K⁆ Module.End K (UniversalEnvelopingAlgebra K L) :=
  (Algebra.lmul K (UniversalEnvelopingAlgebra K L)).toLieHom.comp
    (UniversalEnvelopingAlgebra.ι K)

private def adoSemidirectRepresentation
    {K I H : Type*} [Field K] [LieRing I] [LieAlgebra K I]
    [LieRing H] [LieAlgebra K H] (ψ : H →ₗ⁅K⁆ LieDerivation K I I) :
    (I ⋊⁅ψ⁆ H) →ₗ⁅K⁆ Module.End K (UniversalEnvelopingAlgebra K I) where
  toLinearMap :=
    (adoLeftRegularLie (K := K) (L := I)).toLinearMap.comp
        (LieAlgebra.SemiDirectSum.projl ψ) +
      ((adoExtendDerivationHom (K := K) (L := I)).comp ψ).toLinearMap.comp
        (LieAlgebra.SemiDirectSum.projr ψ).toLinearMap
  map_lie' := by
    intro x y
    ext u
    change
      UniversalEnvelopingAlgebra.ι K
            (⁅x.left, y.left⁆ + ψ x.right y.left - ψ y.right x.left) * u +
          adoExtendDerivation (ψ ⁅x.right, y.right⁆) u =
        (UniversalEnvelopingAlgebra.ι K x.left *
              (UniversalEnvelopingAlgebra.ι K y.left * u +
                adoExtendDerivation (ψ y.right) u) +
            adoExtendDerivation (ψ x.right)
              (UniversalEnvelopingAlgebra.ι K y.left * u +
                adoExtendDerivation (ψ y.right) u)) -
          (UniversalEnvelopingAlgebra.ι K y.left *
              (UniversalEnvelopingAlgebra.ι K x.left * u +
                adoExtendDerivation (ψ x.right) u) +
            adoExtendDerivation (ψ y.right)
              (UniversalEnvelopingAlgebra.ι K x.left * u +
                adoExtendDerivation (ψ x.right) u))
    rw [LieHom.map_lie ψ]
    have hlie := LinearMap.congr_fun
      (adoExtendDerivation_lie (ψ x.right) (ψ y.right)) u
    change adoExtendDerivation ⁅ψ x.right, ψ y.right⁆ u =
      adoExtendDerivation (ψ x.right) (adoExtendDerivation (ψ y.right) u) -
        adoExtendDerivation (ψ y.right) (adoExtendDerivation (ψ x.right) u) at hlie
    rw [hlie]
    simp only [map_add, map_sub, LieHom.map_lie, adoExtendDerivation_mul,
      adoExtendDerivation_ι, Ring.lie_def]
    noncomm_ring

private abbrev adoUEA
    (K L : Type*) [CommRing K] [LieRing L] [LieAlgebra K L] :=
  UniversalEnvelopingAlgebra K L

private noncomputable def adoWord
    {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    {d : ℕ} (b : Module.Basis (Fin d) K L) (w : List (Fin d)) : adoUEA K L :=
  (w.map fun i => UniversalEnvelopingAlgebra.ι K (b i)).prod

@[simp] private theorem adoWord_nil
    {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    {d : ℕ} (b : Module.Basis (Fin d) K L) : adoWord b [] = 1 := rfl

@[simp] private theorem adoWord_cons
    {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    {d : ℕ} (b : Module.Basis (Fin d) K L) (i : Fin d) (w : List (Fin d)) :
    adoWord b (i :: w) = UniversalEnvelopingAlgebra.ι K (b i) * adoWord b w := rfl

private theorem adoWord_append
    {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    {d : ℕ} (b : Module.Basis (Fin d) K L) (u v : List (Fin d)) :
    adoWord b (u ++ v) = adoWord b u * adoWord b v := by
  simp [adoWord, List.map_append]

private def adoWordsLt
    {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    {d : ℕ} (b : Module.Basis (Fin d) K L) (n : ℕ) : Set (adoUEA K L) :=
  {u | ∃ w : List (Fin d), w.length < n ∧ adoWord b w = u}

private theorem adoWord_mem_wordsLt
    {K L : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    {d : ℕ} (b : Module.Basis (Fin d) K L) {w : List (Fin d)} {n : ℕ}
    (hw : w.length < n) : adoWord b w ∈ adoWordsLt b n :=
  ⟨w, hw, rfl⟩

private theorem adoMul_word_mem_span_wordsLt
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    {d : ℕ} (b : Module.Basis (Fin d) K L) {u : adoUEA K L} {n : ℕ}
    (hu : u ∈ Submodule.span K (adoWordsLt b n)) (v : List (Fin d)) :
    u * adoWord b v ∈ Submodule.span K (adoWordsLt b (n + v.length)) := by
  refine Submodule.span_induction (p := fun u _ =>
      u * adoWord b v ∈ Submodule.span K (adoWordsLt b (n + v.length))) ?_ ?_ ?_ ?_ hu
  · intro u hu
    obtain ⟨w, hw, rfl⟩ := hu
    rw [← adoWord_append]
    apply Submodule.subset_span
    exact adoWord_mem_wordsLt b (by simp; omega)
  · simp
  · intro x y _ _ hx hy
    simpa [add_mul] using Submodule.add_mem _ hx hy
  · intro c x _ hx
    simpa [Algebra.smul_mul_assoc] using Submodule.smul_mem
      (Submodule.span K (adoWordsLt b (n + v.length))) c hx

private theorem adoWord_mul_mem_span_wordsLt
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    {d : ℕ} (b : Module.Basis (Fin d) K L) (v : List (Fin d))
    {u : adoUEA K L} {n : ℕ} (hu : u ∈ Submodule.span K (adoWordsLt b n)) :
    adoWord b v * u ∈ Submodule.span K (adoWordsLt b (v.length + n)) := by
  refine Submodule.span_induction (p := fun u _ =>
      adoWord b v * u ∈ Submodule.span K (adoWordsLt b (v.length + n))) ?_ ?_ ?_ ?_ hu
  · intro u hu
    obtain ⟨w, hw, rfl⟩ := hu
    rw [← adoWord_append]
    apply Submodule.subset_span
    exact adoWord_mem_wordsLt b (by simp; omega)
  · simp
  · intro x y _ _ hx hy
    simpa [mul_add] using Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [Algebra.mul_smul_comm]
    exact Submodule.smul_mem _ c hx

private theorem adoIota_mem_span_wordsLt
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    {d : ℕ} (b : Module.Basis (Fin d) K L) (x : L) :
    UniversalEnvelopingAlgebra.ι K x ∈ Submodule.span K (adoWordsLt b 2) := by
  rw [← b.sum_repr x]
  simp only [map_sum, map_smul]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  apply Submodule.subset_span
  simpa [adoWord] using adoWord_mem_wordsLt b (w := [i]) (n := 2) (by simp)

private theorem adoWord_sub_word_mem_span_wordsLt_of_perm
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    {d : ℕ} (b : Module.Basis (Fin d) K L) {u v : List (Fin d)} (h : u.Perm v) :
    adoWord b u - adoWord b v ∈ Submodule.span K (adoWordsLt b u.length) := by
  induction h with
  | nil => simp
  | cons i h ih =>
      rw [adoWord_cons, adoWord_cons, ← mul_sub]
      have hm := adoWord_mul_mem_span_wordsLt b [i] ih
      simpa [Nat.add_comm] using hm
  | swap i j w =>
      simp only [adoWord_cons]
      rw [← mul_assoc, ← mul_assoc, ← sub_mul]
      have hrel :
          UniversalEnvelopingAlgebra.ι K (b j) * UniversalEnvelopingAlgebra.ι K (b i) -
              UniversalEnvelopingAlgebra.ι K (b i) * UniversalEnvelopingAlgebra.ι K (b j) =
            UniversalEnvelopingAlgebra.ι K ⁅b j, b i⁆ := by
        simpa only [Ring.lie_def] using
          (LieHom.map_lie (UniversalEnvelopingAlgebra.ι K) (b j) (b i)).symm
      rw [hrel]
      have hi := adoIota_mem_span_wordsLt b ⁅b j, b i⁆
      have hm := adoMul_word_mem_span_wordsLt b hi w
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hm
  | trans h₁ h₂ ih₁ ih₂ =>
      have hsum := Submodule.add_mem _ ih₁ (by simpa [h₁.length_eq] using ih₂)
      rw [sub_add_sub_cancel] at hsum
      exact hsum

private theorem adoExists_replicate_perm {d B : ℕ} [NeZero d] (w : List (Fin d))
    (h : d * B ≤ w.length) :
    ∃ i : Fin d, ∃ rest, w.Perm (List.replicate B i ++ rest) := by
  let v : List.Vector (Fin d) w.length := ⟨w, rfl⟩
  obtain ⟨i, hi⟩ := Fintype.exists_le_card_fiber_of_mul_le_card
    (fun j : Fin w.length => v.get j) (by simpa using h)
  have hicount : B ≤ w.count i := by
    rw [Fin.card_filter_univ_eq_vector_get_eq_count i v] at hi
    simpa [v] using hi
  have hsub : (List.replicate B i).Sublist w :=
    List.replicate_sublist_iff.mpr hicount
  obtain ⟨rest, hperm⟩ := hsub.exists_perm_append
  exact ⟨i, rest, hperm⟩

private def adoModWords
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    {d : ℕ} (Q : Ideal (adoUEA K L)) (b : Module.Basis (Fin d) K L) (n : ℕ) :
    Submodule K (adoUEA K L) :=
  (Q : Submodule (adoUEA K L) (adoUEA K L)).restrictScalars K ⊔
    Submodule.span K (adoWordsLt b n)

private theorem adoModWords_mul_word
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    {d : ℕ} (Q : Ideal (adoUEA K L)) [Q.IsTwoSided]
    (b : Module.Basis (Fin d) K L) {u : adoUEA K L} {n : ℕ}
    (hu : u ∈ adoModWords Q b n) (v : List (Fin d)) :
    u * adoWord b v ∈ adoModWords Q b (n + v.length) := by
  obtain ⟨q, hq, s, hs, rfl⟩ := Submodule.mem_sup.mp hu
  rw [add_mul]
  apply Submodule.add_mem
  · apply Submodule.mem_sup_left
    exact Q.mul_mem_right _ hq
  · apply Submodule.mem_sup_right
    exact adoMul_word_mem_span_wordsLt b hs v

private theorem adoLong_word_mem_modWords
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    {d B : ℕ} [NeZero d] (Q : Ideal (adoUEA K L)) [Q.IsTwoSided]
    (b : Module.Basis (Fin d) K L)
    (hpow : ∀ i : Fin d,
      (UniversalEnvelopingAlgebra.ι K (b i)) ^ B ∈ adoModWords Q b B)
    (w : List (Fin d)) (hw : d * B ≤ w.length) :
    adoWord b w ∈ adoModWords Q b w.length := by
  obtain ⟨i, rest, hperm⟩ := adoExists_replicate_perm w hw
  let block := List.replicate B i ++ rest
  have hlen : block.length = w.length := hperm.length_eq.symm
  have hdiff : adoWord b w - adoWord b block ∈ adoModWords Q b w.length := by
    apply Submodule.mem_sup_right
    exact adoWord_sub_word_mem_span_wordsLt_of_perm b hperm
  have hblock : adoWord b block ∈ adoModWords Q b w.length := by
    have hm := adoModWords_mul_word Q b (hpow i) rest
    have hword : adoWord b block =
        (UniversalEnvelopingAlgebra.ι K (b i)) ^ B * adoWord b rest := by
      simp [block, adoWord]
    rw [hword]
    have hsum : B + rest.length = w.length := by simpa [block] using hlen
    rw [hsum] at hm
    exact hm
  have heq : adoWord b w = (adoWord b w - adoWord b block) + adoWord b block := by abel
  rw [heq]
  exact Submodule.add_mem _ hdiff hblock

private theorem adoWord_mem_bounded_modWords
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    {d B : ℕ} [NeZero d] (Q : Ideal (adoUEA K L)) [Q.IsTwoSided]
    (b : Module.Basis (Fin d) K L)
    (hpow : ∀ i : Fin d,
      (UniversalEnvelopingAlgebra.ι K (b i)) ^ B ∈ adoModWords Q b B)
    (w : List (Fin d)) : adoWord b w ∈ adoModWords Q b (d * B) := by
  induction hlen : w.length using Nat.strong_induction_on generalizing w with
  | h n ih =>
      by_cases hw : w.length < d * B
      · apply Submodule.mem_sup_right
        exact Submodule.subset_span (adoWord_mem_wordsLt b hw)
      · have hlong := adoLong_word_mem_modWords Q b hpow w (Nat.le_of_not_gt hw)
        obtain ⟨q, hq, s, hs, hqs⟩ := Submodule.mem_sup.mp hlong
        rw [← hqs]
        apply Submodule.add_mem
        · exact Submodule.mem_sup_left hq
        · refine Submodule.span_induction (p := fun s _ => s ∈ adoModWords Q b (d * B))
            ?_ (Submodule.zero_mem _) (fun _ _ _ _ => Submodule.add_mem _)
            (fun c _ _ h => Submodule.smul_mem _ c h) hs
          rintro u ⟨v, hv, rfl⟩
          exact ih v.length (by simpa [hlen] using hv) v rfl

private def adoAllWords
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    {d : ℕ} (b : Module.Basis (Fin d) K L) : Set (adoUEA K L) :=
  Set.range (adoWord b)

private theorem adoWord_mem_span_allWords
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    {d : ℕ} (b : Module.Basis (Fin d) K L) (w : List (Fin d)) :
    adoWord b w ∈ Submodule.span K (adoAllWords b) :=
  Submodule.subset_span ⟨w, rfl⟩

private theorem adoSpan_allWords_mul
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    {d : ℕ} (b : Module.Basis (Fin d) K L) {u v : adoUEA K L}
    (hu : u ∈ Submodule.span K (adoAllWords b))
    (hv : v ∈ Submodule.span K (adoAllWords b)) :
    u * v ∈ Submodule.span K (adoAllWords b) := by
  refine Submodule.span_induction (p := fun u _ =>
      u * v ∈ Submodule.span K (adoAllWords b)) ?_ ?_ ?_ ?_ hu
  · rintro _ ⟨w, rfl⟩
    refine Submodule.span_induction (p := fun v _ =>
        adoWord b w * v ∈ Submodule.span K (adoAllWords b)) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨z, rfl⟩
      rw [← adoWord_append]
      exact adoWord_mem_span_allWords b (w ++ z)
    · simp
    · intro x y _ _ hx hy
      simpa [mul_add] using Submodule.add_mem _ hx hy
    · intro c x _ hx
      rw [Algebra.mul_smul_comm]
      exact Submodule.smul_mem _ c hx
  · simp
  · intro x y _ _ hx hy
    simpa [add_mul] using Submodule.add_mem _ hx hy
  · intro c x _ hx
    simpa [Algebra.smul_mul_assoc] using Submodule.smul_mem
      (Submodule.span K (adoAllWords b)) c hx

private theorem adoIota_mem_span_allWords
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    {d : ℕ} (b : Module.Basis (Fin d) K L) (x : L) :
    UniversalEnvelopingAlgebra.ι K x ∈ Submodule.span K (adoAllWords b) := by
  rw [← b.sum_repr x]
  simp only [map_sum, map_smul]
  apply Submodule.sum_mem
  intro i hi
  apply Submodule.smul_mem
  simpa [adoWord] using adoWord_mem_span_allWords b [i]

private theorem adoUEA_mem_span_allWords
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    {d : ℕ} (b : Module.Basis (Fin d) K L) (u : adoUEA K L) :
    u ∈ Submodule.span K (adoAllWords b) := by
  obtain ⟨t, ht⟩ := RingCon.mkₐ_surjective (α := K)
    (UniversalEnvelopingAlgebra.ringCon K L) u
  subst u
  change UniversalEnvelopingAlgebra.mkAlgHom K L t ∈ Submodule.span K (adoAllWords b)
  induction t using TensorAlgebra.induction with
  | algebraMap r =>
      change algebraMap K (adoUEA K L) r ∈ Submodule.span K (adoAllWords b)
      rw [Algebra.algebraMap_eq_smul_one]
      exact Submodule.smul_mem _ r (by simpa using adoWord_mem_span_allWords b [])
  | ι x => exact adoIota_mem_span_allWords b x
  | mul x y hx hy => exact adoSpan_allWords_mul b hx hy
  | add x y hx hy => exact Submodule.add_mem _ hx hy

private theorem adoUEA_mem_bounded_modWords
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    {d B : ℕ} [NeZero d] (Q : Ideal (adoUEA K L)) [Q.IsTwoSided]
    (b : Module.Basis (Fin d) K L)
    (hpow : ∀ i : Fin d,
      (UniversalEnvelopingAlgebra.ι K (b i)) ^ B ∈ adoModWords Q b B)
    (u : adoUEA K L) : u ∈ adoModWords Q b (d * B) := by
  refine Submodule.span_induction (p := fun u _ => u ∈ adoModWords Q b (d * B))
    ?_ (Submodule.zero_mem _) (fun _ _ _ _ => Submodule.add_mem _)
    (fun c _ _ h => Submodule.smul_mem _ c h) (adoUEA_mem_span_allWords b u)
  rintro _ ⟨w, rfl⟩
  exact adoWord_mem_bounded_modWords Q b hpow w

private theorem adoWordsLt_finite
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    {d : ℕ} (b : Module.Basis (Fin d) K L) (n : ℕ) :
    (adoWordsLt b n).Finite := by
  have h := (List.finite_length_lt (Fin d) n).image (adoWord b)
  apply h.subset
  rintro u ⟨w, hw, rfl⟩
  exact ⟨w, hw, rfl⟩

private theorem adoQuotient_finite_of_power_relations
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    {d B : ℕ} (Q : Ideal (adoUEA K L)) [Q.IsTwoSided]
    (b : Module.Basis (Fin d) K L)
    (hpow : ∀ i : Fin d,
      (UniversalEnvelopingAlgebra.ι K (b i)) ^ B ∈ adoModWords Q b B) :
    Module.Finite K (adoUEA K L ⧸
      (Q : Submodule (adoUEA K L) (adoUEA K L)).restrictScalars K) := by
  let qK := (Q : Submodule (adoUEA K L) (adoUEA K L)).restrictScalars K
  by_cases hd : d = 0
  · subst d
    have hall : adoAllWords b = {1} := by
      ext u
      constructor
      · rintro ⟨w, rfl⟩
        have hw : w = [] := Subsingleton.elim w []
        subst w
        simp
      · rintro (rfl)
        exact ⟨[], by simp⟩
    let S := Submodule.span K (adoAllWords b)
    have hS : S = ⊤ := by
      apply top_unique
      intro u _
      exact adoUEA_mem_span_allWords b u
    let _ : Module.Finite K S := Module.Finite.span_of_finite K (by
      rw [hall]
      exact Set.finite_singleton 1)
    have hsurj : Function.Surjective S.subtype := by
      intro u
      refine ⟨⟨u, ?_⟩, rfl⟩
      rw [hS]
      exact Submodule.mem_top
    let _ : Module.Finite K (adoUEA K L) :=
      Module.Finite.of_surjective S.subtype hsurj
    exact Module.Finite.of_surjective qK.mkQ
      (Submodule.Quotient.mk_surjective qK)
  · let _ : NeZero d := ⟨hd⟩
    let S := Submodule.span K (adoWordsLt b (d * B))
    let f : S →ₗ[K] adoUEA K L ⧸ qK := qK.mkQ.comp S.subtype
    let _ : Module.Finite K S :=
      Module.Finite.span_of_finite K (adoWordsLt_finite b (d * B))
    apply Module.Finite.of_surjective f
    intro z
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective qK z
    have hu := adoUEA_mem_bounded_modWords Q b hpow u
    obtain ⟨q, hq, s, hs, hqs⟩ := Submodule.mem_sup.mp hu
    refine ⟨⟨s, hs⟩, ?_⟩
    apply (Submodule.Quotient.eq qK).mpr
    change s - u ∈ qK
    rw [← hqs]
    simpa using qK.neg_mem hq

private theorem adoUEA_lift_preserves
    {K L V : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
    (W : LieSubmodule K L V) (u : adoUEA K L) {v : V} (hv : v ∈ W) :
    UniversalEnvelopingAlgebra.lift K (LieModule.toEnd K L V) u v ∈ W := by
  let φ := UniversalEnvelopingAlgebra.lift K (LieModule.toEnd K L V)
  obtain ⟨t, ht⟩ := RingCon.mkₐ_surjective (α := K)
    (UniversalEnvelopingAlgebra.ringCon K L) u
  subst u
  change φ (UniversalEnvelopingAlgebra.mkAlgHom K L t) v ∈ W
  revert v
  induction t using TensorAlgebra.induction with
  | algebraMap r =>
      intro v hv
      simpa using W.smul_mem r hv
  | ι x =>
      intro v hv
      simpa [φ] using W.lie_mem hv
  | mul x y hx hy =>
      intro v hv
      rw [map_mul, map_mul, Module.End.mul_apply]
      change φ (UniversalEnvelopingAlgebra.mkAlgHom K L x)
          (φ (UniversalEnvelopingAlgebra.mkAlgHom K L y) v) ∈ W
      exact hx (hy hv)
  | add x y hx hy =>
      intro v hv
      rw [map_add, map_add]
      simpa using W.add_mem (hx hv) (hy hv)

private theorem adoTwoSidedSpan_lowers_lcs
    {K L V : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
    (I : LieIdeal K L) (S : Set (adoUEA K L))
    (hS : ∀ s ∈ S, ∀ j v, v ∈ I.lcs V j →
      UniversalEnvelopingAlgebra.lift K (LieModule.toEnd K L V) s v ∈
        I.lcs V (j + 1))
    {t : adoUEA K L} (ht : t ∈ TwoSidedIdeal.span S) (j : ℕ) {v : V}
    (hv : v ∈ I.lcs V j) :
    UniversalEnvelopingAlgebra.lift K (LieModule.toEnd K L V) t v ∈
      I.lcs V (j + 1) := by
  let φ := UniversalEnvelopingAlgebra.lift K (LieModule.toEnd K L V)
  refine TwoSidedIdeal.span_induction (p := fun t _ =>
      ∀ j v, v ∈ I.lcs V j → φ t v ∈ I.lcs V (j + 1))
      ?_ ?_ ?_ ?_ ?_ ?_ ht j v hv
  · intro s hs
    exact hS s hs
  · simp
  · intro x y _ _ hx hy j v hv
    simpa using (I.lcs V (j + 1)).add_mem (hx j v hv) (hy j v hv)
  · intro x _ hx j v hv
    simpa using (I.lcs V (j + 1)).neg_mem (hx j v hv)
  · intro a x _ hx j v hv
    rw [map_mul, Module.End.mul_apply]
    change φ a (φ x v) ∈ I.lcs V (j + 1)
    exact adoUEA_lift_preserves (I.lcs V (j + 1)) a (hx j v hv)
  · intro b x _ hx j v hv
    rw [map_mul, Module.End.mul_apply]
    change φ x (φ b v) ∈ I.lcs V (j + 1)
    exact hx j (φ b v) (adoUEA_lift_preserves (I.lcs V j) b hv)

private theorem adoIdealPower_lowers_lcs
    {K L V : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
    (I : LieIdeal K L) (S : Set (adoUEA K L))
    (hS : ∀ s ∈ S, ∀ j v, v ∈ I.lcs V j →
      UniversalEnvelopingAlgebra.lift K (LieModule.toEnd K L V) s v ∈
        I.lcs V (j + 1))
    (k j : ℕ) {t : adoUEA K L}
    (ht : t ∈ (TwoSidedIdeal.span S).asIdeal ^ k) {v : V}
    (hv : v ∈ I.lcs V j) :
    UniversalEnvelopingAlgebra.lift K (LieModule.toEnd K L V) t v ∈
      I.lcs V (j + k) := by
  let φ := UniversalEnvelopingAlgebra.lift K (LieModule.toEnd K L V)
  induction k generalizing t j v with
  | zero =>
      simpa using adoUEA_lift_preserves (I.lcs V j) t hv
  | succ k ih =>
      rw [Ideal.IsTwoSided.pow_succ] at ht
      refine Submodule.mul_induction_on ht ?_ ?_
      · intro x hx y hy
        rw [map_mul, Module.End.mul_apply]
        change φ x (φ y v) ∈ I.lcs V (j + (k + 1))
        have hyv := ih j hy hv
        have hxv := adoTwoSidedSpan_lowers_lcs I S hS
          (TwoSidedIdeal.mem_asIdeal.mp hx) (j + k) hyv
        simpa [Nat.add_assoc] using hxv
      · intro x y hx hy
        simpa using (I.lcs V (j + (k + 1))).add_mem hx hy

private theorem adoIdealPower_le_ker_lift
    {K L V : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup V] [Module K V] [LieRingModule L V] [LieModule K L V]
    (I : LieIdeal K L) (S : Set (adoUEA K L))
    (hS : ∀ s ∈ S, ∀ j v, v ∈ I.lcs V j →
      UniversalEnvelopingAlgebra.lift K (LieModule.toEnd K L V) s v ∈
        I.lcs V (j + 1))
    (k : ℕ) (hk : I.lcs V k = ⊥) :
    (((TwoSidedIdeal.span S).asIdeal ^ k : Ideal (adoUEA K L)) :
      Submodule (adoUEA K L) (adoUEA K L)).restrictScalars K ≤
        LinearMap.ker (UniversalEnvelopingAlgebra.lift K
          (LieModule.toEnd K L V)).toLinearMap := by
  intro t ht
  rw [LinearMap.mem_ker]
  ext v
  rw [LinearMap.zero_apply]
  have h := adoIdealPower_lowers_lcs I S hS k 0 ht (v := v)
    (by simp [LieIdeal.lcs_zero])
  simpa [hk] using h

private theorem adoDerivation_pow_mul_eq_zero
    {K A : Type*} [Field K] [Ring A] [Algebra K A]
    (d : Module.End K A) (hd : ∀ x y, d (x * y) = x * d y + d x * y)
    {x y : A} {a b : ℕ} (hx : (d ^ a) x = 0) (hy : (d ^ b) y = 0) :
    (d ^ (a + b)) (x * y) = 0 := by
  induction h : a + b using Nat.strong_induction_on generalizing a b x y with
  | h n ih =>
      subst n
      obtain rfl | a := a
      · have hx0 : x = 0 := by simpa using hx
        subst x
        simp
      obtain rfl | b := b
      · have hy0 : y = 0 := by simpa using hy
        subst y
        simp
      have hdx : (d ^ a) (d x) = 0 := by
        simpa [pow_succ, Module.End.mul_apply] using hx
      have hdy : (d ^ b) (d y) = 0 := by
        simpa [pow_succ, Module.End.mul_apply] using hy
      have h₁ : (d ^ (a.succ + b)) (x * d y) = 0 :=
        ih (a.succ + b) (by omega) (a := a.succ) (b := b) hx hdy rfl
      have h₂ : (d ^ (a + b.succ)) (d x * y) = 0 :=
        ih (a + b.succ) (by omega) (a := a) (b := b.succ) hdx hy rfl
      have h₁' : (d ^ (a + b + 1)) (x * d y) = 0 := by
        rw [show a + b + 1 = a.succ + b by omega]
        exact h₁
      have h₂' : (d ^ (a + b + 1)) (d x * y) = 0 := by
        rw [show a + b + 1 = a + b.succ by omega]
        exact h₂
      rw [show a.succ + b.succ = (a + b + 1) + 1 by omega,
        pow_succ, Module.End.mul_apply, hd, map_add]
      rw [h₁', h₂', add_zero]

private theorem adoDerivation_locallyNilpotent_add
    {K A : Type*} [Field K] [AddCommGroup A] [Module K A]
    (d : Module.End K A) {x y : A}
    (hx : ∃ n, (d ^ n) x = 0) (hy : ∃ n, (d ^ n) y = 0) :
    ∃ n, (d ^ n) (x + y) = 0 := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  refine ⟨a + b, ?_⟩
  rw [map_add]
  have hax : (d ^ (a + b)) x = 0 := by
    rw [show a + b = b + a by omega, pow_add, Module.End.mul_apply, ha, map_zero]
  have hby : (d ^ (a + b)) y = 0 := by
    rw [pow_add, Module.End.mul_apply, hb, map_zero]
  rw [hax, hby, add_zero]

private theorem adoDerivation_locallyNilpotent_mul
    {K A : Type*} [Field K] [Ring A] [Algebra K A]
    (d : Module.End K A) (hd : ∀ x y, d (x * y) = x * d y + d x * y)
    {x y : A} (hx : ∃ n, (d ^ n) x = 0) (hy : ∃ n, (d ^ n) y = 0) :
    ∃ n, (d ^ n) (x * y) = 0 := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  exact ⟨a + b, adoDerivation_pow_mul_eq_zero d hd ha hb⟩

private theorem adoUEA_derivation_locallyNilpotent
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    (D : Module.End K L) (d : Module.End K (adoUEA K L))
    (hd : ∀ u v, d (u * v) = u * d v + d u * v)
    (hι : ∀ x, d (UniversalEnvelopingAlgebra.ι K x) =
      UniversalEnvelopingAlgebra.ι K (D x))
    (hD : IsNilpotent D) (u : adoUEA K L) :
    ∃ n, (d ^ n) u = 0 := by
  have hd1 : d 1 = 0 := by
    have h := hd 1 1
    simp only [one_mul, mul_one] at h
    have h' := congrArg (fun z => z - d 1) h
    simpa using h'.symm
  have hscalar (c : K) : d (algebraMap K (adoUEA K L) c) = 0 := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, hd1, smul_zero]
  have hιpow (n : ℕ) (x : L) :
      (d ^ n) (UniversalEnvelopingAlgebra.ι K x) =
        UniversalEnvelopingAlgebra.ι K ((D ^ n) x) := by
    induction n generalizing x with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, Module.End.mul_apply, hι, pow_succ,
          Module.End.mul_apply]
        exact ih (D x)
  obtain ⟨r, hr⟩ := hD
  obtain ⟨t, ht⟩ := RingCon.mkₐ_surjective (α := K)
    (UniversalEnvelopingAlgebra.ringCon K L) u
  subst u
  change ∃ n, (d ^ n) (UniversalEnvelopingAlgebra.mkAlgHom K L t) = 0
  induction t using TensorAlgebra.induction with
  | algebraMap c =>
      refine ⟨1, ?_⟩
      change d (algebraMap K (adoUEA K L) c) = 0
      exact hscalar c
  | ι x =>
      refine ⟨r, ?_⟩
      change (d ^ r) (UniversalEnvelopingAlgebra.ι K x) = 0
      rw [hιpow, LinearMap.congr_fun hr x, LinearMap.zero_apply, map_zero]
  | mul x y hx hy =>
      rw [map_mul]
      exact adoDerivation_locallyNilpotent_mul d hd hx hy
  | add x y hx hy =>
      rw [map_add]
      exact adoDerivation_locallyNilpotent_add d hx hy

private theorem adoEnd_isNilpotent_of_locallyNilpotent
    {K M : Type*} [Field K] [AddCommGroup M] [Module K M] [Module.Finite K M]
    (f : Module.End K M) (hlocal : ∀ x, ∃ n, (f ^ n) x = 0) :
    IsNilpotent f := by
  classical
  obtain ⟨m, s, hs⟩ := Module.Finite.exists_fin (R := K) (M := M)
  choose e he using fun i : Fin m => hlocal (s i)
  let N := ∑ i : Fin m, e i
  have hei (i : Fin m) : e i ≤ N := by
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hkill (i : Fin m) : (f ^ N) (s i) = 0 := by
    have hi := hei i
    rw [show N = (N - e i) + e i by omega, pow_add, Module.End.mul_apply,
      he i, map_zero]
  refine ⟨N, LinearMap.ker_eq_top.mp ?_⟩
  apply top_unique
  rw [← hs]
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  change (f ^ N) (s i) = 0
  exact hkill i

private theorem adoUEA_derivation_mem_ideal
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    (d : Module.End K (adoUEA K L))
    (hd : ∀ u v, d (u * v) = u * d v + d u * v)
    (T : Ideal (adoUEA K L)) [T.IsTwoSided]
    (hι : ∀ x, d (UniversalEnvelopingAlgebra.ι K x) ∈ T)
    (u : adoUEA K L) : d u ∈ T := by
  have hd1 : d 1 = 0 := by
    have h := hd 1 1
    simp only [one_mul, mul_one] at h
    have h' := congrArg (fun z => z - d 1) h
    simpa using h'.symm
  obtain ⟨t, ht⟩ := RingCon.mkₐ_surjective (α := K)
    (UniversalEnvelopingAlgebra.ringCon K L) u
  subst u
  change d (UniversalEnvelopingAlgebra.mkAlgHom K L t) ∈ T
  induction t using TensorAlgebra.induction with
  | algebraMap c =>
      change d (algebraMap K (adoUEA K L) c) ∈ T
      rw [Algebra.algebraMap_eq_smul_one, map_smul, hd1, smul_zero]
      exact T.zero_mem
  | ι x => exact hι x
  | mul x y hx hy =>
      rw [map_mul, hd]
      exact T.add_mem (T.mul_mem_left _ hy) (T.mul_mem_right _ hx)
  | add x y hx hy =>
      rw [map_add, map_add]
      exact T.add_mem hx hy

private theorem adoUEA_derivation_preserves_idealPower
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    (d : Module.End K (adoUEA K L))
    (hd : ∀ u v, d (u * v) = u * d v + d u * v)
    (T : Ideal (adoUEA K L)) [T.IsTwoSided]
    (hT : ∀ u, d u ∈ T) (k : ℕ) {u : adoUEA K L} (hu : u ∈ T ^ k) :
    d u ∈ T ^ k := by
  induction k generalizing u with
  | zero =>
      rw [Submodule.pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
  | succ k ih =>
      rw [Ideal.IsTwoSided.pow_succ] at hu ⊢
      refine Submodule.mul_induction_on hu ?_ ?_
      · intro x hx y hy
        rw [hd]
        exact Submodule.add_mem _
          (Submodule.mul_mem_mul hx (ih hy))
          (Submodule.mul_mem_mul (hT x) hy)
      · intro x y hx hy
        simpa using Submodule.add_mem _ hx hy

private theorem adoQuotient_end_isNilpotent
    {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (d : Module.End K M) (P : Submodule K M) (hP : P ≤ P.comap d)
    [Module.Finite K (M ⧸ P)]
    (hlocal : ∀ x, ∃ n, (d ^ n) x = 0) :
    IsNilpotent (P.mapQ P d hP) := by
  apply adoEnd_isNilpotent_of_locallyNilpotent
  intro q
  induction q using Quotient.inductionOn' with
  | _ x =>
      obtain ⟨n, hn⟩ := hlocal x
      refine ⟨n, ?_⟩
      rw [← P.mapQ_pow]
      change (Submodule.Quotient.mk ((d ^ n) x) : M ⧸ P) = 0
      rw [hn]
      rfl

private def adoQuotientRepresentation
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M]
    (ρ : L →ₗ⁅K⁆ Module.End K M) (P : Submodule K M)
    (hP : ∀ x, P ≤ P.comap (ρ x)) :
    L →ₗ⁅K⁆ Module.End K (M ⧸ P) where
  toLinearMap :=
    { toFun := fun x => P.mapQ P (ρ x) (hP x)
      map_add' := by
        intro x y
        ext m
        change (Submodule.Quotient.mk (ρ (x + y) m) : M ⧸ P) =
          Submodule.Quotient.mk (ρ x m) + Submodule.Quotient.mk (ρ y m)
        simp
      map_smul' := by
        intro c x
        ext m
        change (Submodule.Quotient.mk (ρ (c • x) m) : M ⧸ P) =
          c • Submodule.Quotient.mk (ρ x m)
        simp }
  map_lie' := by
    intro x y
    ext m
    change (Submodule.Quotient.mk (ρ ⁅x, y⁆ m) : M ⧸ P) =
      Submodule.Quotient.mk (ρ x (ρ y m)) -
        Submodule.Quotient.mk (ρ y (ρ x m))
    rw [LieHom.map_lie ρ]
    change Submodule.Quotient.mk ((ρ x (ρ y m)) - (ρ y (ρ x m))) = _
    rfl

private noncomputable def adoSemidirectEquivOfIsCompl
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    (I : LieIdeal K L) (H : LieSubalgebra K L)
    (hc : IsCompl I.toSubmodule H.toSubmodule) :
    (I ⋊⁅(adoIdealAd I).comp H.incl⁆ H) ≃ₗ⁅K⁆ L where
  __ := (LieAlgebra.SemiDirectSum.toProdl ((adoIdealAd I).comp H.incl)).trans
    (I.toSubmodule.prodEquivOfIsCompl H.toSubmodule hc)
  map_lie' := by
    intro x y
    change
      (⁅(x.left : L), (y.left : L)⁆ + ⁅(x.right : L), (y.left : L)⁆ -
          ⁅(y.right : L), (x.left : L)⁆ : L) + ⁅(x.right : L), (y.right : L)⁆ =
        ⁅(x.left : L) + x.right, (y.left : L) + y.right⁆
    simp only [lie_add, add_lie]
    have hskew : -⁅(y.right : L), (x.left : L)⁆ =
        ⁅(x.left : L), (y.right : L)⁆ := by
      rw [lie_skew]
    rw [sub_eq_add_neg, hskew]
    abel

private theorem adoEnd_isNilpotent_of_restrict_quotient
    {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (f : Module.End K M) (P : Submodule K M) (hP : P ≤ P.comap f)
    (hres : IsNilpotent (f.restrict hP))
    (hquot : IsNilpotent (P.mapQ P f hP)) : IsNilpotent f := by
  obtain ⟨a, ha⟩ := hquot
  obtain ⟨b, hb⟩ := hres
  refine ⟨a + b, ?_⟩
  ext m
  have hfam : (f ^ a) m ∈ P := by
    have hz := LinearMap.congr_fun ha (Submodule.Quotient.mk m)
    rw [LinearMap.zero_apply, ← P.mapQ_pow, Submodule.mapQ_apply,
      Submodule.Quotient.mk_eq_zero] at hz
    exact hz
  have hb' := LinearMap.congr_fun hb ⟨(f ^ a) m, hfam⟩
  rw [Module.End.pow_restrict, LinearMap.zero_apply] at hb'
  change (f ^ (a + b)) m = 0
  rw [show a + b = b + a by omega, pow_add, Module.End.mul_apply]
  exact congrArg Subtype.val hb'

private theorem adoLieModule_isNilpotent_of_submodule_quotient
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [Module.Finite K M] (P : LieSubmodule K L M)
    (hP : LieModule.IsNilpotent L P)
    (hquot : LieModule.IsNilpotent L (M ⧸ P)) :
    LieModule.IsNilpotent L M := by
  rw [LieModule.isNilpotent_iff_forall' (R := K)] at hP hquot ⊢
  intro x
  let f := LieModule.toEnd K L M x
  let hf : P.toSubmodule ≤ P.toSubmodule.comap f := fun _ hm => P.lie_mem hm
  exact adoEnd_isNilpotent_of_restrict_quotient f P.toSubmodule hf
    (hP x) (hquot x)

private theorem adoNilpotent_of_codim_one_extension
    {K L M : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    [Module.Finite K M]
    (A : LieIdeal K L) (h : L)
    (hdecomp : ∀ x : L, ∃ a : A, ∃ c : K, x = a.1 + c • h)
    (hA : LieModule.IsNilpotent A M)
    (hh : IsNilpotent (LieModule.toEnd K L M h)) :
    LieModule.IsNilpotent L M := by
  classical
  by_cases hM : Subsingleton M
  · let _ : Subsingleton M := hM
    infer_instance
  · let _ : Nontrivial M := not_subsingleton_iff_nontrivial.mp hM
    let F : LieSubmodule K L M := A.lcs M 1
    have hFne : F ≠ ⊤ := by
      intro hF
      obtain ⟨k, hk⟩ := (LieModule.isNilpotent_iff K A M).mp hA
      have hk' : A.lcs M k = ⊥ := by
        rw [← LieSubmodule.toSubmodule_inj, LieIdeal.coe_lcs_eq, hk]
        rfl
      have hall : ∀ n, A.lcs M n = ⊤ := by
        intro n
        induction n with
        | zero => simp [LieIdeal.lcs_zero]
        | succ n ih =>
            rw [show n + 1 = n.succ by rfl, LieIdeal.lcs_succ, ih]
            simpa [F] using hF
      have := (hall k).symm.trans hk'
      exact bot_ne_top this.symm
    have hfin : Module.finrank K F < Module.finrank K M :=
      Submodule.finrank_lt (by
        intro htop
        apply hFne
        rw [← LieSubmodule.toSubmodule_inj]
        exact htop)
    have hAF : LieModule.IsNilpotent A F := by
      rw [LieModule.isNilpotent_iff_forall' (R := K)] at hA ⊢
      intro a
      exact Module.End.isNilpotent.restrict
        (fun _ hm => F.lie_mem hm) (hA a)
    have hhF : IsNilpotent (LieModule.toEnd K L F h) := by
      exact Module.End.isNilpotent.restrict (fun _ hm => F.lie_mem hm) hh
    have hFL : LieModule.IsNilpotent L F :=
      adoNilpotent_of_codim_one_extension A h hdecomp hAF hhF
    have hpres : F.toSubmodule ≤
        F.toSubmodule.comap (LieModule.toEnd K L M h) := fun _ hm => F.lie_mem hm
    have hhquot : IsNilpotent (LieModule.toEnd K L (M ⧸ F) h) := by
      exact Module.End.IsNilpotent.mapQ hpres hh
    have hquot : LieModule.IsNilpotent L (M ⧸ F) := by
      rw [LieModule.isNilpotent_iff_forall' (R := K)]
      intro x
      obtain ⟨a, c, rfl⟩ := hdecomp x
      have ha0 : LieModule.toEnd K L (M ⧸ F) a.1 = 0 := by
        ext q
        induction q using Quotient.inductionOn' with
        | _ m =>
            rw [LinearMap.zero_apply]
            change (Submodule.Quotient.mk ⁅a.1, m⁆ : M ⧸ F) = 0
            rw [Submodule.Quotient.mk_eq_zero]
            change ⁅a.1, m⁆ ∈ F
            rw [show F = ⁅A, (⊤ : LieSubmodule K L M)⁆ from by
              simp [F, LieIdeal.lcs_succ]]
            exact LieSubmodule.lie_mem_lie a.2 (LieSubmodule.mem_top m)
      rw [map_add, map_smul, ha0, zero_add]
      exact hhquot.smul c
    exact adoLieModule_isNilpotent_of_submodule_quotient F hFL hquot
termination_by Module.finrank K M
decreasing_by exact hfin

open LieAlgebra
open scoped TensorProduct

private def adoRestrictIdeal
    {K L M : Type*} [CommRing K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup M] [Module K M] [LieRingModule L M] [LieModule K L M]
    (N : LieSubmodule K L M) (I : LieIdeal K L) : LieSubmodule K I M where
  carrier := N
  add_mem' := N.add_mem'
  zero_mem' := N.zero_mem'
  smul_mem' := N.smul_mem'
  lie_mem hm := N.lie_mem hm

private abbrev adoCommutatorIdeal
    {K G : Type*} [CommRing K] [LieRing G] [LieAlgebra K G]
    (I : LieIdeal K G) : LieIdeal K G :=
  ⁅(⊤ : LieIdeal K G), I⁆

private theorem adoCommutator_weightSpace_le_maxTriv
    {K G M : Type*} [Field K] [CharZero K] [LieRing G] [LieAlgebra K G]
    [AddCommGroup M] [Module K M] [LieRingModule G M] [LieModule K G M]
    [Module.Finite K M]
    (I : LieIdeal K G) (χ : Module.Dual K I) :
    adoRestrictIdeal (LieModule.weightSpaceOfIsLieTower K M χ) (adoCommutatorIdeal I) ≤
      LieModule.maxTrivSubmodule K (adoCommutatorIdeal I) M := by
  intro m hm
  rw [LieModule.mem_maxTrivSubmodule]
  intro x
  change m ∈ LieModule.weightSpace M χ at hm
  have hm' : ∀ a : I, ⁅a.1, m⁆ = χ a • m := by
    simpa [LieModule.mem_weightSpace] using hm
  have hzm (z : G) : ⁅z, m⁆ ∈ LieModule.weightSpace M χ := by
    exact (LieModule.weightSpaceOfIsLieTower K M χ).lie_mem hm
  have hgenerator (z : G) (a : I) : ⁅⁅z, a.1⁆, m⁆ = 0 := by
    rw [lie_lie, hm' a, lie_smul]
    have ha : ⁅a.1, ⁅z, m⁆⁆ = χ a • ⁅z, m⁆ := by
      exact (LieModule.mem_weightSpace χ _).mp (hzm z) a
    rw [ha, sub_self]
  let f : G →ₗ[K] M :=
    (LinearMap.applyₗ (R := K) m).comp (LieModule.toEnd K G M).toLinearMap
  have hle : (adoCommutatorIdeal I : Submodule K G) ≤ LinearMap.ker f := by
    rw [show (adoCommutatorIdeal I : Submodule K G) =
        Submodule.span K {y | ∃ (z : (⊤ : LieIdeal K G)) (a : I), ⁅z.1, a.1⁆ = y} from
      LieSubmodule.lieIdeal_oper_eq_linear_span (I : LieSubmodule K G G)
        (⊤ : LieIdeal K G)]
    apply Submodule.span_le.mpr
    rintro y ⟨z, a, rfl⟩
    exact hgenerator z.1 a
  have hxker := hle x.2
  change f x.1 = 0 at hxker
  simpa [f, LieModule.toEnd_apply_apply] using hxker

private theorem adoCommutator_acts_nilpotently_algClosed
    (K G M : Type*) [Field K] [CharZero K] [IsAlgClosed K]
    [LieRing G] [LieAlgebra K G]
    [AddCommGroup M] [Module K M] [LieRingModule G M] [LieModule K G M]
    [Module.Finite K M] (I : LieIdeal K G) [LieAlgebra.IsSolvable I] :
    LieModule.IsNilpotent (adoCommutatorIdeal I) M := by
  classical
  by_cases hM : Subsingleton M
  · let _ : Subsingleton M := hM
    infer_instance
  · let _ : Nontrivial M := not_subsingleton_iff_nontrivial.mp hM
    obtain ⟨χ, hχ⟩ := LieModule.exists_nontrivial_weightSpace_of_isSolvable K I M
    let W : LieSubmodule K G M := LieModule.weightSpaceOfIsLieTower K M χ
    by_cases hW : W = ⊤
    · have htop : LieModule.maxTrivSubmodule K (adoCommutatorIdeal I) M = ⊤ := by
        rw [← top_le_iff]
        intro m hm
        apply adoCommutator_weightSpace_le_maxTriv I χ
        change m ∈ W
        rw [hW]
        exact LieSubmodule.mem_top m
      let _ : LieModule.IsTrivial (adoCommutatorIdeal I) M :=
        (LieModule.isTrivial_iff_max_triv_eq_top K (adoCommutatorIdeal I) M).mpr htop
      infer_instance
    · have hfin : Module.finrank K (M ⧸ W) < Module.finrank K M := by
        rw [← Submodule.finrank_quotient_add_finrank W.toSubmodule]
        exact Nat.lt_add_of_pos_right
          ((Module.finrank_pos_iff_of_free K W).mpr hχ)
      have hquot : LieModule.IsNilpotent (adoCommutatorIdeal I) (M ⧸ W) :=
        adoCommutator_acts_nilpotently_algClosed K G (M ⧸ W) I
      apply LieModule.nilpotentOfNilpotentQuotient K (adoCommutatorIdeal I) M
          (N := adoRestrictIdeal W (adoCommutatorIdeal I))
      · exact adoCommutator_weightSpace_le_maxTriv (M := M) I χ
      · exact hquot
termination_by Module.finrank K M
decreasing_by exact hfin

private theorem adoCommutator_acts_nilpotently
    {K G M : Type*} [Field K] [CharZero K]
    [LieRing G] [LieAlgebra K G]
    [AddCommGroup M] [Module K M] [LieRingModule G M] [LieModule K G M]
    [Module.Finite K M] (I : LieIdeal K G) [LieAlgebra.IsSolvable I] :
    LieModule.IsNilpotent (adoCommutatorIdeal I) M := by
  set A := AlgebraicClosure (FractionRing K)
  have _i : FaithfulSMul K A := FaithfulSMul.trans K (FractionRing K) A
  let IA : LieIdeal A (A ⊗[K] G) := I.baseChange A
  let _ : LieAlgebra.IsSolvable IA := by
    obtain ⟨k, hk⟩ := LieAlgebra.IsSolvable.solvable K I
    apply LieAlgebra.IsSolvable.mk (R := A)
    rw [LieIdeal.derivedSeries_eq_bot_iff,
      LieAlgebra.derivedSeriesOfIdeal_baseChange]
    · have hk' : LieAlgebra.derivedSeriesOfIdeal K G k I = ⊥ :=
        (I.derivedSeries_eq_bot_iff k).mp hk
      rw [hk', LieSubmodule.baseChange_bot]
  have nilp_ext : LieModule.IsNilpotent
      (adoCommutatorIdeal IA) (A ⊗[K] M) :=
    adoCommutator_acts_nilpotently_algClosed A (A ⊗[K] G) (A ⊗[K] M) IA
  rw [LieModule.isNilpotent_iff_forall' (R := K)]
  rw [LieModule.isNilpotent_iff_forall' (R := A)] at nilp_ext
  intro ⟨x, hx⟩
  have hx_ext : 1 ⊗ₜ[K] x ∈ adoCommutatorIdeal IA := by
    have hIA : adoCommutatorIdeal IA = (adoCommutatorIdeal I).baseChange A := by
      dsimp [IA, adoCommutatorIdeal]
      rw [LieSubmodule.lie_baseChange, LieSubmodule.baseChange_top]
    rw [hIA]
    exact LieSubmodule.tmul_mem_baseChange_of_mem 1 hx
  have hbc_inj : Function.Injective (Module.End.baseChangeHom K A M) :=
    LinearMap.baseChangeHom_injective K M A
  have aux : (LieModule.toEnd K (adoCommutatorIdeal I) M ⟨x, hx⟩).baseChangeHom K A M =
      (LieModule.toEnd K G M x).baseChange A := rfl
  rw [← IsNilpotent.map_iff hbc_inj, aux, ← LieModule.toEnd_baseChange]
  exact nilp_ext ⟨_, hx_ext⟩

private theorem adoCommutator_isNilpotent
    {K G : Type*} [Field K] [CharZero K]
    [LieRing G] [LieAlgebra K G] [Module.Finite K G]
    (I : LieIdeal K G) [LieAlgebra.IsSolvable I] :
    LieRing.IsNilpotent (↑(⁅(⊤ : LieIdeal K G), I⁆ : LieIdeal K G)) := by
  rw [LieAlgebra.isNilpotent_iff_forall (R := K)]
  intro x
  apply LieSubalgebra.isNilpotent_ad_of_isNilpotent_ad
    (adoCommutatorIdeal I : LieSubalgebra K G)
  exact (LieModule.isNilpotent_iff_forall' (R := K)).mp
    (adoCommutator_acts_nilpotently (M := G) I) x

private def adoQuotientLieHom
    {K B : Type*} [CommRing K] [LieRing B] [LieAlgebra K B]
    (C : LieIdeal K B) : B →ₗ⁅K⁆ B ⧸ C where
  toLinearMap := C.toSubmodule.mkQ
  map_lie' := by intros; rfl

private theorem adoAdd_center_isNilpotent
    {K G : Type*} [Field K] [LieRing G] [LieAlgebra K G]
    (J : LieIdeal K G) [LieRing.IsNilpotent J] :
    LieRing.IsNilpotent (J + LieAlgebra.center K G : LieIdeal K G) := by
  let B : LieIdeal K G := J + LieAlgebra.center K G
  let C : LieIdeal K B := (LieAlgebra.center K G).comap B.incl
  have hC : C ≤ LieAlgebra.center K B := by
    intro z hz
    rw [LieModule.mem_maxTrivSubmodule]
    intro b
    apply Subtype.ext
    change ⁅(b.1 : G), (z.1 : G)⁆ = 0
    have hzG : (z.1 : G) ∈ LieAlgebra.center K G := hz
    exact (LieModule.mem_maxTrivSubmodule K G G (z.1 : G)).mp hzG b.1
  apply LieAlgebra.nilpotent_of_nilpotent_quotient hC
  let f : J →ₗ⁅K⁆ B ⧸ C :=
    (adoQuotientLieHom C).comp (LieIdeal.inclusion (show J ≤ B from le_sup_left))
  refine Function.Surjective.lieAlgebra_isNilpotent (f := f) ?_
  intro q
  induction q using Quotient.inductionOn' with
  | _ b =>
      have hb : (b.1 : G) ∈ J.toSubmodule ⊔ (LieAlgebra.center K G).toSubmodule := b.2
      obtain ⟨j, hj, z, hz, hjz⟩ := Submodule.mem_sup.mp hb
      refine ⟨⟨j, hj⟩, ?_⟩
      apply (Submodule.Quotient.eq C.toSubmodule).mpr
      have hjB : j ∈ B := Submodule.mem_sup_left hj
      let jb : B := ⟨j, hjB⟩
      change jb - b ∈ C
      change (j - b.1 : G) ∈ LieAlgebra.center K G
      rw [← hjz]
      simpa using (LieAlgebra.center K G).neg_mem hz

private theorem ado_transport_fin_nilpotent
    {K L V : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    (ρ : L →ₗ⁅K⁆ Module.End K V) (hρ : Function.Injective ρ)
    (hnil : ∀ x, IsNilpotent (ρ x)) :
    ∃ (n : ℕ) (ρ' : L →ₗ⁅K⁆ Module.End K (Fin n → K)),
      Function.Injective ρ' ∧ ∀ x, IsNilpotent (ρ' x) := by
  let _ : Module.Free K V := Module.Free.of_divisionRing K V
  let e := (Module.finBasis K V).equivFun
  refine ⟨Module.finrank K V, e.lieConj.comp ρ,
    e.lieConj.injective.comp hρ, ?_⟩
  intro x
  obtain ⟨k, hk⟩ := hnil x
  refine ⟨k, ?_⟩
  change (e.conjAlgEquiv K (ρ x)) ^ k = 0
  rw [← map_pow, hk, map_zero]

private theorem ado_transport_fin_nilpotent_on
    {K L V : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup V] [Module K V] [Module.Finite K V]
    (N : LieIdeal K L)
    (ρ : L →ₗ⁅K⁆ Module.End K V) (hρ : Function.Injective ρ)
    (hnil : ∀ x : N, IsNilpotent (ρ x.1)) :
    ∃ (n : ℕ) (ρ' : L →ₗ⁅K⁆ Module.End K (Fin n → K)),
      Function.Injective ρ' ∧ ∀ x : N, IsNilpotent (ρ' x.1) := by
  let _ : Module.Free K V := Module.Free.of_divisionRing K V
  let e := (Module.finBasis K V).equivFun
  refine ⟨Module.finrank K V, e.lieConj.comp ρ,
    e.lieConj.injective.comp hρ, ?_⟩
  intro x
  obtain ⟨k, hk⟩ := hnil x
  refine ⟨k, ?_⟩
  change (e.conjAlgEquiv K (ρ x.1)) ^ k = 0
  rw [← map_pow, hk, map_zero]

private theorem adoDirectSum_isNilpotent
    {K L V W : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    (ρ : L →ₗ⁅K⁆ Module.End K V) (σ : L →ₗ⁅K⁆ Module.End K W)
    {x : L} (hρ : IsNilpotent (ρ x)) (hσ : IsNilpotent (σ x)) :
    IsNilpotent (adoDirectSum ρ σ x) := by
  obtain ⟨a, ha⟩ := hρ
  obtain ⟨b, hb⟩ := hσ
  refine ⟨a + b, ?_⟩
  have ha' : ρ x ^ (a + b) = 0 := by
    rw [pow_add, ha, zero_mul]
  have hb' : σ x ^ (a + b) = 0 := by
    rw [pow_add, hb, mul_zero]
  change ((LinearMap.prodMapAlgHom K V W) (ρ x, σ x)) ^ (a + b) = 0
  rw [← map_pow]
  have hp : (ρ x, σ x) ^ (a + b) = 0 := by
    ext <;> simp [ha', hb']
  rw [hp, map_zero]

private def adoLineSubalgebra
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] (h : L) :
    LieSubalgebra K L where
  toSubmodule := K ∙ h
  lie_mem' := by
    intro x y hx hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
    simp

private theorem adoLine_isLieAbelian
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] (h : L) :
    IsLieAbelian (adoLineSubalgebra (K := K) h) := by
  constructor
  intro x y
  apply Subtype.ext
  obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp x.2
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp y.2
  change ⁅(x : L), (y : L)⁆ = 0
  rw [← ha, ← hb]
  simp

private theorem adoCoatom_decomp
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    (A : LieIdeal K L) (hA : IsCoatom A.toSubmodule) (h : L) (hh : h ∉ A) :
    ∀ x : L, ∃ a : A, ∃ c : K, x = a.1 + c • h := by
  intro x
  have hc : IsCompl A.toSubmodule (K ∙ h) :=
    Submodule.isCompl_span_singleton_of_isCoatom_of_notMem hA hh
  obtain ⟨a, z, ha, hz, rfl⟩ :=
    Submodule.codisjoint_iff_exists_add_eq.mp hc.codisjoint x
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
  exact ⟨⟨a, ha⟩, c, rfl⟩

private theorem adoSemidirectRepresentation_preserves_ideal
    {K I H : Type*} [Field K] [LieRing I] [LieAlgebra K I]
    [LieRing H] [LieAlgebra K H] (ψ : H →ₗ⁅K⁆ LieDerivation K I I)
    (Q : Ideal (adoUEA K I)) [Q.IsTwoSided]
    (hQ : ∀ h u, u ∈ Q → adoExtendDerivation (ψ h) u ∈ Q) (x : I ⋊⁅ψ⁆ H) :
    (Q : Submodule (adoUEA K I) (adoUEA K I)).restrictScalars K ≤
      ((Q : Submodule (adoUEA K I) (adoUEA K I)).restrictScalars K).comap
        (adoSemidirectRepresentation ψ x) := by
  intro u hu
  change UniversalEnvelopingAlgebra.ι K x.left * u +
      adoExtendDerivation (ψ x.right) u ∈ Q
  exact Q.add_mem (Q.mul_mem_left _ hu) (hQ x.right u hu)

private theorem adoSemidirectQuotient_faithful_left
    {K I H V : Type*} [Field K] [LieRing I] [LieAlgebra K I]
    [LieRing H] [LieAlgebra K H]
    [AddCommGroup V] [Module K V]
    (ψ : H →ₗ⁅K⁆ LieDerivation K I I)
    (ρ : I →ₗ⁅K⁆ Module.End K V) (hρ : Function.Injective ρ)
    (Q : Ideal (adoUEA K I)) [Q.IsTwoSided]
    (hQker :
      (Q : Submodule (adoUEA K I) (adoUEA K I)).restrictScalars K ≤
        LinearMap.ker (UniversalEnvelopingAlgebra.lift K ρ).toLinearMap)
    (hQ : ∀ h u, u ∈ Q → adoExtendDerivation (ψ h) u ∈ Q)
    (a : I)
    (ha : adoQuotientRepresentation (adoSemidirectRepresentation ψ)
      ((Q : Submodule (adoUEA K I) (adoUEA K I)).restrictScalars K)
      (adoSemidirectRepresentation_preserves_ideal ψ Q hQ) ⟨a, 0⟩ = 0) :
    a = 0 := by
  let qK := (Q : Submodule (adoUEA K I) (adoUEA K I)).restrictScalars K
  have ha1 := LinearMap.congr_fun ha (Submodule.Quotient.mk (1 : adoUEA K I))
  have hDz : adoExtendDerivation (ψ (0 : H)) = 0 := by
    change adoExtendDerivationHom (ψ 0) = 0
    rw [map_zero, map_zero]
  have hrep : adoSemidirectRepresentation ψ (⟨a, 0⟩ : I ⋊⁅ψ⁆ H)
      (1 : adoUEA K I) = UniversalEnvelopingAlgebra.ι K a := by
    change UniversalEnvelopingAlgebra.ι K a * 1 +
      adoExtendDerivation (ψ 0) 1 = _
    rw [hDz]
    simp
  have hiota : UniversalEnvelopingAlgebra.ι K a ∈ Q := by
    rw [LinearMap.zero_apply] at ha1
    change (Submodule.Quotient.mk
      (adoSemidirectRepresentation ψ (⟨a, 0⟩ : I ⋊⁅ψ⁆ H) 1) :
        adoUEA K I ⧸ qK) = 0 at ha1
    rw [hrep] at ha1
    rw [Submodule.Quotient.mk_eq_zero] at ha1
    exact ha1
  have hzero := hQker hiota
  rw [LinearMap.mem_ker] at hzero
  have hι : UniversalEnvelopingAlgebra.lift K ρ
      (UniversalEnvelopingAlgebra.ι K a) = ρ a :=
    UniversalEnvelopingAlgebra.lift_ι_apply K ρ a
  change UniversalEnvelopingAlgebra.lift K ρ
    (UniversalEnvelopingAlgebra.ι K a) = 0 at hzero
  rw [hι] at hzero
  exact hρ (hzero.trans (map_zero ρ).symm)

private theorem adoQuotient_end_isNilpotent_of_pow_mem
    {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (d : Module.End K M) (P : Submodule K M) (hP : P ≤ P.comap d)
    (k : ℕ) (hk : ∀ x, (d ^ k) x ∈ P) :
    IsNilpotent (P.mapQ P d hP) := by
  refine ⟨k, ?_⟩
  ext x
  rw [← P.mapQ_pow]
  change (Submodule.Quotient.mk ((d ^ k) x) : M ⧸ P) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  exact hk x

private theorem adoSemidirectQuotient_left_isNilpotent
    {K I H : Type*} [Field K] [LieRing I] [LieAlgebra K I]
    [LieRing H] [LieAlgebra K H] (ψ : H →ₗ⁅K⁆ LieDerivation K I I)
    (Q : Ideal (adoUEA K I)) [Q.IsTwoSided]
    (hQ : ∀ h u, u ∈ Q → adoExtendDerivation (ψ h) u ∈ Q)
    (a : I) (k : ℕ) (hpow : (UniversalEnvelopingAlgebra.ι K a) ^ k ∈ Q) :
    IsNilpotent
      (adoQuotientRepresentation (adoSemidirectRepresentation ψ)
        ((Q : Submodule (adoUEA K I) (adoUEA K I)).restrictScalars K)
        (adoSemidirectRepresentation_preserves_ideal ψ Q hQ) ⟨a, 0⟩) := by
  let qK := (Q : Submodule (adoUEA K I) (adoUEA K I)).restrictScalars K
  let d : Module.End K (adoUEA K I) :=
    Algebra.lmul K (adoUEA K I) (UniversalEnvelopingAlgebra.ι K a)
  have hdQ : qK ≤ qK.comap d := by
    intro u hu
    exact Q.mul_mem_left _ hu
  have hdk : ∀ u, (d ^ k) u ∈ qK := by
    intro u
    change ((Algebra.lmul K (adoUEA K I)
      (UniversalEnvelopingAlgebra.ι K a)) ^ k) u ∈ Q
    rw [← map_pow]
    exact Q.mul_mem_right u hpow
  have hnil := adoQuotient_end_isNilpotent_of_pow_mem d qK hdQ k hdk
  have hDz : adoExtendDerivation (ψ (0 : H)) = 0 := by
    change adoExtendDerivationHom (ψ 0) = 0
    rw [map_zero, map_zero]
  have hrep : adoSemidirectRepresentation ψ (⟨a, 0⟩ : I ⋊⁅ψ⁆ H) = d := by
    ext u
    change UniversalEnvelopingAlgebra.ι K a * u +
      adoExtendDerivation (ψ 0) u = UniversalEnvelopingAlgebra.ι K a * u
    rw [hDz]
    simp
  have hmap : qK.mapQ qK
      (adoSemidirectRepresentation ψ (⟨a, 0⟩ : I ⋊⁅ψ⁆ H))
      (adoSemidirectRepresentation_preserves_ideal ψ Q hQ ⟨a, 0⟩) =
      qK.mapQ qK d hdQ := by
    ext u
    change (Submodule.Quotient.mk
      (adoSemidirectRepresentation ψ (⟨a, 0⟩ : I ⋊⁅ψ⁆ H) u) :
        adoUEA K I ⧸ qK) = Submodule.Quotient.mk (d u)
    rw [hrep]
  change IsNilpotent (qK.mapQ qK
    (adoSemidirectRepresentation ψ (⟨a, 0⟩ : I ⋊⁅ψ⁆ H))
    (adoSemidirectRepresentation_preserves_ideal ψ Q hQ ⟨a, 0⟩))
  rw [hmap]
  exact hnil

private theorem adoSemidirectQuotient_right_isNilpotent
    {K I H : Type*} [Field K] [LieRing I] [LieAlgebra K I]
    [LieRing H] [LieAlgebra K H] (ψ : H →ₗ⁅K⁆ LieDerivation K I I)
    (Q : Ideal (adoUEA K I)) [Q.IsTwoSided]
    (hQ : ∀ h u, u ∈ Q → adoExtendDerivation (ψ h) u ∈ Q)
    [Module.Finite K (adoUEA K I ⧸
      (Q : Submodule (adoUEA K I) (adoUEA K I)).restrictScalars K)]
    (h : H) (hD : IsNilpotent (ψ h).toLinearMap) :
    IsNilpotent
      (adoQuotientRepresentation (adoSemidirectRepresentation ψ)
        ((Q : Submodule (adoUEA K I) (adoUEA K I)).restrictScalars K)
        (adoSemidirectRepresentation_preserves_ideal ψ Q hQ) ⟨0, h⟩) := by
  let qK := (Q : Submodule (adoUEA K I) (adoUEA K I)).restrictScalars K
  let d : Module.End K (adoUEA K I) := adoExtendDerivation (ψ h)
  have hdQ : qK ≤ qK.comap d := hQ h
  have hlocal : ∀ u, ∃ n, (d ^ n) u = 0 := by
    exact adoUEA_derivation_locallyNilpotent (ψ h).toLinearMap d
      (adoExtendDerivation_mul (ψ h)) (adoExtendDerivation_ι (ψ h)) hD
  have hnil := adoQuotient_end_isNilpotent d qK hdQ hlocal
  have hrep : adoSemidirectRepresentation ψ (⟨0, h⟩ : I ⋊⁅ψ⁆ H) = d := by
    ext u
    change UniversalEnvelopingAlgebra.ι K 0 * u +
      adoExtendDerivation (ψ h) u = adoExtendDerivation (ψ h) u
    simp
  have hmap : qK.mapQ qK
      (adoSemidirectRepresentation ψ (⟨0, h⟩ : I ⋊⁅ψ⁆ H))
      (adoSemidirectRepresentation_preserves_ideal ψ Q hQ ⟨0, h⟩) =
      qK.mapQ qK d hdQ := by
    ext u
    change (Submodule.Quotient.mk
      (adoSemidirectRepresentation ψ (⟨0, h⟩ : I ⋊⁅ψ⁆ H) u) :
        adoUEA K I ⧸ qK) = Submodule.Quotient.mk (d u)
    rw [hrep]
  change IsNilpotent (qK.mapQ qK
    (adoSemidirectRepresentation ψ (⟨0, h⟩ : I ⋊⁅ψ⁆ H))
    (adoSemidirectRepresentation_preserves_ideal ψ Q hQ ⟨0, h⟩))
  rw [hmap]
  exact hnil

private theorem adoNilpotent_exists_coatom
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] [LieRing.IsNilpotent L]
    (hab : ¬ IsLieAbelian L) :
    ∃ (A : LieIdeal K L), IsCoatom A.toSubmodule ∧
      (LieAlgebra.derivedSeries K L 1 : Submodule K L) ≤ A.toSubmodule ∧
      ∃ h : L, h ∉ A := by
  have hnsub : ¬ Subsingleton L := by
    intro hsub
    apply hab
    let _ : Subsingleton L := hsub
    infer_instance
  let _ : Nontrivial L := not_subsingleton_iff_nontrivial.mp hnsub
  have hder := LieAlgebra.derivedSeries_lt_top_of_solvable K L
  obtain htop | ⟨A, hA, hAL⟩ :=
    eq_top_or_exists_le_coatom (LieAlgebra.derivedSeries K L 1).toSubmodule
  · apply (hder.ne ?_).elim
    rw [← LieSubmodule.toSubmodule_inj]
    exact htop
  lift A to LieIdeal K L
  · intro x y hy
    exact hAL (LieSubmodule.lie_mem_lie
      (LieSubmodule.mem_top x) (LieSubmodule.mem_top y))
  obtain ⟨h, -, hh⟩ := SetLike.exists_of_lt hA.lt_top
  exact ⟨A, hA, hAL, h, hh⟩

private theorem adoCoatom_nontrivial
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    (A : LieIdeal K L)
    (hder : (LieAlgebra.derivedSeries K L 1 : Submodule K L) ≤ A.toSubmodule)
    (hab : ¬ IsLieAbelian L) : Nontrivial A := by
  have hxy : ∃ x y : L, ⁅x, y⁆ ≠ 0 := by
    by_contra h
    apply hab
    constructor
    intro x y
    by_contra hxy
    exact h ⟨x, y, hxy⟩
  obtain ⟨x, y, hxy⟩ := hxy
  let a : A := ⟨⁅x, y⁆, hder (LieSubmodule.lie_mem_lie
    (LieSubmodule.mem_top x) (LieSubmodule.mem_top y))⟩
  exact ⟨⟨a, 0, fun ha => hxy (congrArg Subtype.val ha)⟩⟩

private theorem adoAeval_monic_mem_modWords
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    {d : ℕ} (Q : Ideal (adoUEA K L)) [Q.IsTwoSided]
    (b : Module.Basis (Fin d) K L) (i : Fin d) (p : Polynomial K) (hp : p.Monic)
    (hrel : Polynomial.aeval (UniversalEnvelopingAlgebra.ι K (b i)) p ∈ Q) :
    (UniversalEnvelopingAlgebra.ι K (b i)) ^ p.natDegree ∈
      adoModWords Q b p.natDegree := by
  let x := UniversalEnvelopingAlgebra.ι K (b i)
  let n := p.natDegree
  change x ^ n ∈ adoModWords Q b n
  let r := ∑ j ∈ Finset.range n,
    Polynomial.C (p.coeff j) * Polynomial.X ^ j
  have hlow : Polynomial.aeval x r ∈
      Submodule.span K (adoWordsLt b n) := by
    dsimp [r]
    rw [map_sum]
    apply Submodule.sum_mem
    intro j hj
    rw [map_mul, map_pow, Polynomial.aeval_C, Polynomial.aeval_X]
    change p.coeff j • x ^ j ∈ Submodule.span K (adoWordsLt b n)
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨List.replicate j i, by simpa using (Finset.mem_range.mp hj), ?_⟩
    simp [x, adoWord]
  have hpas : p = Polynomial.X ^ n + r := by
    simpa [n, r] using hp.as_sum
  have heval : Polynomial.aeval x p =
      x ^ n + Polynomial.aeval x r := by
    rw [hpas, map_add, map_pow, Polynomial.aeval_X]
  have hx : x ^ n = Polynomial.aeval x p - Polynomial.aeval x r := by
    rw [heval]
    abel
  rw [hx]
  exact Submodule.sub_mem _ (Submodule.mem_sup_left hrel)
    (Submodule.mem_sup_right hlow)

private theorem adoIdeal_exists_coatom
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    (N : LieIdeal K L)
    (hderived : (LieAlgebra.derivedSeries K L 1 : Submodule K L) ≤ N.toSubmodule)
    (hN : N ≠ ⊤) :
    ∃ (A : LieIdeal K L), IsCoatom A.toSubmodule ∧ N ≤ A ∧
      ∃ h : L, h ∉ A := by
  have hN' : N.toSubmodule ≠ ⊤ := by
    intro h
    apply hN
    rw [← LieSubmodule.toSubmodule_inj]
    exact h
  obtain htop | ⟨A, hA, hNA⟩ := eq_top_or_exists_le_coatom N.toSubmodule
  · exact (hN' htop).elim
  lift A to LieIdeal K L
  · intro x y hy
    exact hNA (hderived (LieSubmodule.lie_mem_lie
      (LieSubmodule.mem_top x) (LieSubmodule.mem_top y)))
  obtain ⟨h, -, hh⟩ := SetLike.exists_of_lt hA.lt_top
  exact ⟨A, hA, hNA, h, hh⟩

private theorem adoNilpotent_representation
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] [LieRing.IsNilpotent L] :
    ∃ (n : ℕ) (ρ : L →ₗ⁅K⁆ Module.End K (Fin n → K)),
      Function.Injective ρ ∧ ∀ x, IsNilpotent (ρ x) := by
  classical
  by_cases hab : IsLieAbelian L
  · let _ : IsLieAbelian L := hab
    apply ado_transport_fin_nilpotent (adoAbelianShear (K := K) (L := L))
      adoAbelianShear_injective
    intro x
    refine ⟨2, ?_⟩
    rw [pow_two, adoAbelianShear_mul_eq_zero]
  · obtain ⟨A, hA, hder, h, hh⟩ :=
      adoNilpotent_exists_coatom (K := K) (L := L) hab
    let _ : Nontrivial A := adoCoatom_nontrivial (K := K) A hder hab
    have hfin : Module.finrank K A < Module.finrank K L := by
      rw [← finrank_top K L]
      exact Submodule.finrank_lt_finrank_of_lt hA.lt_top
    have hAincl : Function.Injective A.incl := fun x y hxy => Subtype.ext hxy
    let _ : LieRing.IsNilpotent A := hAincl.lieAlgebra_isNilpotent
    obtain ⟨n, ρ₀, hρ₀, hnil₀⟩ :=
      adoNilpotent_representation (K := K) (L := A)
    let V := Fin n → K
    let _ : LieRingModule A V := LieRingModule.compLieHom V ρ₀
    let _ : LieModule K A V := LieModule.compLieHom V ρ₀
    have hVnil : LieModule.IsNilpotent A V := by
      rw [LieModule.isNilpotent_iff_forall' (R := K)]
      intro a
      change IsNilpotent (ρ₀ a)
      exact hnil₀ a
    obtain ⟨k, hk⟩ := (LieModule.isNilpotent_iff K A V).mp hVnil
    let S : Set (adoUEA K A) := Set.range (UniversalEnvelopingAlgebra.ι K)
    let T : Ideal (adoUEA K A) := (TwoSidedIdeal.span S).asIdeal
    let Q : Ideal (adoUEA K A) := T ^ k
    have hgen (a : A) : UniversalEnvelopingAlgebra.ι K a ∈ T := by
      exact TwoSidedIdeal.mem_asIdeal.mpr
        (TwoSidedIdeal.subset_span ⟨a, rfl⟩)
    have hS : ∀ s ∈ S, ∀ j v, v ∈ (⊤ : LieIdeal K A).lcs V j →
        UniversalEnvelopingAlgebra.lift K (LieModule.toEnd K A V) s v ∈
          (⊤ : LieIdeal K A).lcs V (j + 1) := by
      rintro _ ⟨a, rfl⟩ j v hv
      rw [UniversalEnvelopingAlgebra.lift_ι_apply]
      change ⁅a, v⁆ ∈ (⊤ : LieIdeal K A).lcs V (j + 1)
      rw [LieIdeal.lcs_succ]
      exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top a) hv
    have hk' : (⊤ : LieIdeal K A).lcs V k = ⊥ := by
      rw [LieIdeal.lcs_top]
      exact hk
    have hQker :
        (Q : Submodule (adoUEA K A) (adoUEA K A)).restrictScalars K ≤
          LinearMap.ker (UniversalEnvelopingAlgebra.lift K ρ₀).toLinearMap := by
      have htoEnd : LieModule.toEnd K A V = ρ₀ := by rfl
      simpa only [Q, T, S, htoEnd] using
        (adoIdealPower_le_ker_lift (I := (⊤ : LieIdeal K A)) S hS k hk')
    let H : LieSubalgebra K L := adoLineSubalgebra (K := K) h
    have hc : IsCompl A.toSubmodule H.toSubmodule := by
      change IsCompl A.toSubmodule (K ∙ h)
      exact Submodule.isCompl_span_singleton_of_isCoatom_of_notMem hA hh
    let ψ : H →ₗ⁅K⁆ LieDerivation K A A := (adoIdealAd A).comp H.incl
    have hT (z : H) : ∀ u, adoExtendDerivation (ψ z) u ∈ T := by
      apply adoUEA_derivation_mem_ideal (adoExtendDerivation (ψ z))
        (adoExtendDerivation_mul (ψ z)) T
      intro a
      rw [adoExtendDerivation_ι]
      exact hgen ((ψ z) a)
    have hQ : ∀ z u, u ∈ Q → adoExtendDerivation (ψ z) u ∈ Q := by
      intro z u hu
      change adoExtendDerivation (ψ z) u ∈ T ^ k
      exact adoUEA_derivation_preserves_idealPower
        (adoExtendDerivation (ψ z)) (adoExtendDerivation_mul (ψ z))
        T (hT z) k hu
    let b := Module.finBasis K A
    let _ : NeZero (Module.finrank K A) := NeZero.of_pos Module.finrank_pos
    have hpow (i : Fin (Module.finrank K A)) :
        (UniversalEnvelopingAlgebra.ι K (b i)) ^ k ∈ adoModWords Q b k := by
      apply Submodule.mem_sup_left
      change (UniversalEnvelopingAlgebra.ι K (b i)) ^ k ∈ T ^ k
      exact Ideal.pow_mem_pow (hgen (b i)) k
    let qK := (Q : Submodule (adoUEA K A) (adoUEA K A)).restrictScalars K
    let _ : Module.Finite K (adoUEA K A ⧸ qK) :=
      adoQuotient_finite_of_power_relations Q b hpow
    let ρQ : (A ⋊⁅ψ⁆ H) →ₗ⁅K⁆ Module.End K (adoUEA K A ⧸ qK) :=
      adoQuotientRepresentation (adoSemidirectRepresentation ψ) qK
        (adoSemidirectRepresentation_preserves_ideal ψ Q hQ)
    let e : (A ⋊⁅ψ⁆ H) ≃ₗ⁅K⁆ L := adoSemidirectEquivOfIsCompl A H hc
    let ρL : L →ₗ⁅K⁆ Module.End K (adoUEA K A ⧸ qK) := ρQ.comp e.symm
    let hH : H := ⟨h, Submodule.mem_span_singleton_self h⟩
    have heA (a : A) : e.symm a.1 = (⟨a, 0⟩ : A ⋊⁅ψ⁆ H) := by
      apply e.toLinearEquiv.injective
      calc
        e.toLinearEquiv (e.symm.toLinearEquiv a.1) = a.1 :=
          e.apply_symm_apply a.1
        _ = e.toLinearEquiv (⟨a, 0⟩ : A ⋊⁅ψ⁆ H) := by
          change a.1 = a.1 + 0
          simp
    have heh : e.symm h = (⟨0, hH⟩ : A ⋊⁅ψ⁆ H) := by
      apply e.toLinearEquiv.injective
      calc
        e.toLinearEquiv (e.symm.toLinearEquiv h) = h :=
          e.apply_symm_apply h
        _ = e.toLinearEquiv (⟨0, hH⟩ : A ⋊⁅ψ⁆ H) := by
          change h = 0 + h
          simp
    let _ : LieRingModule L (adoUEA K A ⧸ qK) :=
      LieRingModule.compLieHom (adoUEA K A ⧸ qK) ρL
    let _ : LieModule K L (adoUEA K A ⧸ qK) :=
      LieModule.compLieHom (adoUEA K A ⧸ qK) ρL
    have hAnil : LieModule.IsNilpotent A (adoUEA K A ⧸ qK) := by
      rw [LieModule.isNilpotent_iff_forall' (R := K)]
      intro a
      change IsNilpotent (ρL a.1)
      have haQ := adoSemidirectQuotient_left_isNilpotent ψ Q hQ a k
        (show (UniversalEnvelopingAlgebra.ι K a) ^ k ∈ Q from
          Ideal.pow_mem_pow (hgen a) k)
      change IsNilpotent (ρQ (e.symm a.1))
      rw [heA]
      exact haQ
    have had : IsNilpotent (LieModule.toEnd K L L h) :=
      (LieModule.isNilpotent_iff_forall' (R := K)).mp
        (inferInstanceAs (LieRing.IsNilpotent L)) h
    have hD : IsNilpotent (ψ hH).toLinearMap := by
      change IsNilpotent (LieModule.toEnd K L A h)
      exact Module.End.isNilpotent.restrict (fun _ ha => A.lie_mem ha) had
    have hhnil : IsNilpotent (LieModule.toEnd K L (adoUEA K A ⧸ qK) h) := by
      change IsNilpotent (ρL h)
      have hhQ := adoSemidirectQuotient_right_isNilpotent ψ Q hQ hH hD
      change IsNilpotent (ρQ (e.symm h))
      rw [heh]
      exact hhQ
    have hLnil : LieModule.IsNilpotent L (adoUEA K A ⧸ qK) :=
      adoNilpotent_of_codim_one_extension A h
        (adoCoatom_decomp A hA h hh) hAnil hhnil
    let _ : IsLieAbelian H := adoLine_isLieAbelian h
    let σQ : (A ⋊⁅ψ⁆ H) →ₗ⁅K⁆ Module.End K (H × K) :=
      (adoAbelianShear (K := K) (L := H)).comp
        (LieAlgebra.SemiDirectSum.projr ψ)
    let σL : L →ₗ⁅K⁆ Module.End K (H × K) := σQ.comp e.symm
    let ρ := adoDirectSum ρL σL
    have hρ : Function.Injective ρ := by
      intro x y hxy
      have hzero : ρ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      obtain ⟨hleft, hright⟩ :=
        (adoDirectSum_eq_zero_iff ρL σL (x - y)).mp hzero
      let z := e.symm (x - y)
      have hzright : z.right = 0 := by
        apply adoAbelianShear_injective (K := K) (L := H)
        simpa [σL, σQ, z] using hright
      have hzleft : z.left = 0 := by
        apply adoSemidirectQuotient_faithful_left ψ ρ₀ hρ₀ Q hQker hQ
        change ρQ ⟨z.left, 0⟩ = 0
        have hz : z = (⟨z.left, 0⟩ : A ⋊⁅ψ⁆ H) := by
          ext <;> simp [hzright]
        change ρQ (e.symm (x - y)) = 0 at hleft
        change ρQ z = 0 at hleft
        rw [hz] at hleft
        exact hleft
      have hz : z = 0 := by ext <;> simp [hzleft, hzright]
      apply sub_eq_zero.mp
      have hez : e z = x - y := by
        dsimp [z]
        exact e.apply_symm_apply (x - y)
      calc
        x - y = e z := hez.symm
        _ = 0 := by rw [hz, map_zero]
    have hρnil : ∀ x, IsNilpotent (ρ x) := by
      intro x
      apply adoDirectSum_isNilpotent ρL σL
      · change IsNilpotent (LieModule.toEnd K L (adoUEA K A ⧸ qK) x)
        exact (LieModule.isNilpotent_iff_forall' (R := K)).mp hLnil x
      · refine ⟨2, ?_⟩
        rw [pow_two]
        change adoAbelianShear (K := K) (e.symm x).right *
          adoAbelianShear (K := K) (e.symm x).right = 0
        exact adoAbelianShear_mul_eq_zero _ _
    exact ado_transport_fin_nilpotent ρ hρ hρnil
termination_by Module.finrank K L
decreasing_by exact hfin

private theorem adoSolvable_representation
    {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] [LieAlgebra.IsSolvable L]
    (N : LieIdeal K L) [LieRing.IsNilpotent N]
    (hderived : (LieAlgebra.derivedSeries K L 1 : Submodule K L) ≤ N.toSubmodule) :
    ∃ (n : ℕ) (ρ : L →ₗ⁅K⁆ Module.End K (Fin n → K)),
      Function.Injective ρ ∧ ∀ x : N, IsNilpotent (ρ x.1) := by
  classical
  by_cases hab : IsLieAbelian L
  · let _ : IsLieAbelian L := hab
    obtain ⟨n, ρ, hρ, hnil⟩ :=
      ado_transport_fin_nilpotent (adoAbelianShear (K := K) (L := L))
        adoAbelianShear_injective (fun x => ⟨2, by
          rw [pow_two, adoAbelianShear_mul_eq_zero]⟩)
    exact ⟨n, ρ, hρ, fun x => hnil x.1⟩
  · by_cases hN : N = ⊤
    · have hsurj : Function.Surjective N.incl := by
        intro x
        refine ⟨⟨x, ?_⟩, rfl⟩
        rw [hN]
        exact LieSubmodule.mem_top x
      let _ : LieRing.IsNilpotent L := hsurj.lieAlgebra_isNilpotent
      obtain ⟨n, ρ, hρ, hnil⟩ := adoNilpotent_representation (K := K) (L := L)
      exact ⟨n, ρ, hρ, fun x => hnil x.1⟩
    · obtain ⟨A, hA, hNA, h, hh⟩ :=
        adoIdeal_exists_coatom N hderived hN
      let _ : Nontrivial A := adoCoatom_nontrivial A
        (fun _ hx => hNA (hderived hx)) hab
      have hfin : Module.finrank K A < Module.finrank K L := by
        rw [← finrank_top K L]
        exact Submodule.finrank_lt_finrank_of_lt hA.lt_top
      let NA : LieIdeal K A := N.comap A.incl
      let fNA : NA →ₗ⁅K⁆ N :=
        { toLinearMap :=
            { toFun := fun x => ⟨x.1.1, x.2⟩
              map_add' := by intros; rfl
              map_smul' := by intros; rfl }
          map_lie' := by intros; rfl }
      have hfNA : Function.Injective fNA := by
        intro x y hxy
        exact Subtype.ext (Subtype.ext
          (congrArg (fun z : N => (z.1 : L)) hxy))
      let _ : LieRing.IsNilpotent NA := hfNA.lieAlgebra_isNilpotent
      have hderivedA :
          (LieAlgebra.derivedSeries K A 1 : Submodule K A) ≤ NA.toSubmodule := by
        intro x hx
        change x.1 ∈ N
        apply hderived
        apply LieIdeal.derivedSeries_map_le (f := A.incl) 1
        exact LieIdeal.mem_map hx
      obtain ⟨n, ρ₀, hρ₀, hnil₀⟩ :=
        adoSolvable_representation NA hderivedA
      let V := Fin n → K
      let _ : LieRingModule A V := LieRingModule.compLieHom V ρ₀
      let _ : LieModule K A V := LieModule.compLieHom V ρ₀
      have hVnil : LieModule.IsNilpotent NA V := by
        rw [LieModule.isNilpotent_iff_forall' (R := K)]
        intro x
        change IsNilpotent (ρ₀ x.1)
        exact hnil₀ x
      obtain ⟨k, hk⟩ := (LieModule.isNilpotent_iff K NA V).mp hVnil
      let b := Module.finBasis K A
      let p (i : Fin (Module.finrank K A)) : Polynomial K :=
        Polynomial.X * (ρ₀ (b i)).charpoly
      let rel (i : Fin (Module.finrank K A)) : adoUEA K A :=
        Polynomial.aeval (UniversalEnvelopingAlgebra.ι K (b i)) (p i)
      let S : Set (adoUEA K A) :=
        Set.range (fun x : NA => UniversalEnvelopingAlgebra.ι K x.1) ∪
          Set.range rel
      let T : Ideal (adoUEA K A) := (TwoSidedIdeal.span S).asIdeal
      let Q : Ideal (adoUEA K A) := T ^ k
      have hgenN (x : NA) : UniversalEnvelopingAlgebra.ι K x.1 ∈ T := by
        exact TwoSidedIdeal.mem_asIdeal.mpr
          (TwoSidedIdeal.subset_span (Set.mem_union_left _ ⟨x, rfl⟩))
      have hgenRel (i : Fin (Module.finrank K A)) : rel i ∈ T := by
        exact TwoSidedIdeal.mem_asIdeal.mpr
          (TwoSidedIdeal.subset_span (Set.mem_union_right _ ⟨i, rfl⟩))
      have hS : ∀ s ∈ S, ∀ j v, v ∈ NA.lcs V j →
          UniversalEnvelopingAlgebra.lift K (LieModule.toEnd K A V) s v ∈
            NA.lcs V (j + 1) := by
        intro s hs
        rcases hs with hs | hs
        · obtain ⟨x, rfl⟩ := hs
          intro j v hv
          rw [UniversalEnvelopingAlgebra.lift_ι_apply]
          change ⁅x.1, v⁆ ∈ NA.lcs V (j + 1)
          rw [LieIdeal.lcs_succ]
          exact LieSubmodule.lie_mem_lie x.2 hv
        · obtain ⟨i, rfl⟩ := hs
          intro j v hv
          have hzero : UniversalEnvelopingAlgebra.lift K
              (LieModule.toEnd K A V) (rel i) = 0 := by
            dsimp [rel]
            rw [← Polynomial.aeval_algHom_apply,
              UniversalEnvelopingAlgebra.lift_ι_apply]
            change Polynomial.aeval (ρ₀ (b i)) (p i) = 0
            simp [p, LinearMap.aeval_self_charpoly]
          rw [hzero, LinearMap.zero_apply]
          exact (NA.lcs V (j + 1)).zero_mem
      have hk' : NA.lcs V k = ⊥ := by
        rw [← LieSubmodule.toSubmodule_inj, LieIdeal.coe_lcs_eq]
        exact congrArg LieSubmodule.toSubmodule hk
      have hQker :
          (Q : Submodule (adoUEA K A) (adoUEA K A)).restrictScalars K ≤
            LinearMap.ker (UniversalEnvelopingAlgebra.lift K ρ₀).toLinearMap := by
        have htoEnd : LieModule.toEnd K A V = ρ₀ := by rfl
        simpa only [Q, T, htoEnd] using
          (adoIdealPower_le_ker_lift NA S hS k hk')
      let H : LieSubalgebra K L := adoLineSubalgebra (K := K) h
      have hc : IsCompl A.toSubmodule H.toSubmodule := by
        change IsCompl A.toSubmodule (K ∙ h)
        exact Submodule.isCompl_span_singleton_of_isCoatom_of_notMem hA hh
      let ψ : H →ₗ⁅K⁆ LieDerivation K A A := (adoIdealAd A).comp H.incl
      have hT (z : H) : ∀ u, adoExtendDerivation (ψ z) u ∈ T := by
        apply adoUEA_derivation_mem_ideal (adoExtendDerivation (ψ z))
          (adoExtendDerivation_mul (ψ z)) T
        intro a
        rw [adoExtendDerivation_ι]
        have hza : (ψ z a).1 ∈ N := by
          apply hderived
          exact LieSubmodule.lie_mem_lie
            (LieSubmodule.mem_top z.1) (LieSubmodule.mem_top a.1)
        exact hgenN ⟨ψ z a, hza⟩
      have hQ : ∀ z u, u ∈ Q → adoExtendDerivation (ψ z) u ∈ Q := by
        intro z u hu
        change adoExtendDerivation (ψ z) u ∈ T ^ k
        exact adoUEA_derivation_preserves_idealPower
          (adoExtendDerivation (ψ z)) (adoExtendDerivation_mul (ψ z))
          T (hT z) k hu
      let B := k * (Module.finrank K V + 1)
      let _ : NeZero (Module.finrank K A) := NeZero.of_pos Module.finrank_pos
      have hp (i : Fin (Module.finrank K A)) : (p i).Monic := by
        exact Polynomial.monic_X.mul (LinearMap.charpoly_monic (ρ₀ (b i)))
      have hdegree (i : Fin (Module.finrank K A)) : (p i ^ k).natDegree = B := by
        rw [(hp i).natDegree_pow]
        simp [p, B, V, LinearMap.charpoly_natDegree,
          (LinearMap.charpoly_monic (ρ₀ (b i))).ne_zero]
      have hpow (i : Fin (Module.finrank K A)) :
          (UniversalEnvelopingAlgebra.ι K (b i)) ^ B ∈ adoModWords Q b B := by
        have hrelpow : Polynomial.aeval
            (UniversalEnvelopingAlgebra.ι K (b i)) (p i ^ k) ∈ Q := by
          rw [map_pow]
          exact Ideal.pow_mem_pow (hgenRel i) k
        have hm := adoAeval_monic_mem_modWords Q b i (p i ^ k)
          ((hp i).pow k) hrelpow
        rwa [hdegree i] at hm
      let qK := (Q : Submodule (adoUEA K A) (adoUEA K A)).restrictScalars K
      let _ : Module.Finite K (adoUEA K A ⧸ qK) :=
        adoQuotient_finite_of_power_relations Q b hpow
      let ρQ : (A ⋊⁅ψ⁆ H) →ₗ⁅K⁆ Module.End K (adoUEA K A ⧸ qK) :=
        adoQuotientRepresentation (adoSemidirectRepresentation ψ) qK
          (adoSemidirectRepresentation_preserves_ideal ψ Q hQ)
      let e : (A ⋊⁅ψ⁆ H) ≃ₗ⁅K⁆ L := adoSemidirectEquivOfIsCompl A H hc
      let ρL : L →ₗ⁅K⁆ Module.End K (adoUEA K A ⧸ qK) := ρQ.comp e.symm
      let _ : IsLieAbelian H := adoLine_isLieAbelian h
      let σQ : (A ⋊⁅ψ⁆ H) →ₗ⁅K⁆ Module.End K (H × K) :=
        (adoAbelianShear (K := K) (L := H)).comp
          (LieAlgebra.SemiDirectSum.projr ψ)
      let σL : L →ₗ⁅K⁆ Module.End K (H × K) := σQ.comp e.symm
      let ρ := adoDirectSum ρL σL
      have hρ : Function.Injective ρ := by
        intro x y hxy
        have hzero : ρ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
        obtain ⟨hleft, hright⟩ :=
          (adoDirectSum_eq_zero_iff ρL σL (x - y)).mp hzero
        let z := e.symm (x - y)
        have hzright : z.right = 0 := by
          apply adoAbelianShear_injective (K := K) (L := H)
          simpa [σL, σQ, z] using hright
        have hzleft : z.left = 0 := by
          apply adoSemidirectQuotient_faithful_left ψ ρ₀ hρ₀ Q hQker hQ
          change ρQ ⟨z.left, 0⟩ = 0
          have hz : z = (⟨z.left, 0⟩ : A ⋊⁅ψ⁆ H) := by
            ext <;> simp [hzright]
          change ρQ (e.symm (x - y)) = 0 at hleft
          change ρQ z = 0 at hleft
          rw [hz] at hleft
          exact hleft
        have hz : z = 0 := by ext <;> simp [hzleft, hzright]
        apply sub_eq_zero.mp
        have hez : e z = x - y := by
          dsimp [z]
          exact e.apply_symm_apply (x - y)
        calc
          x - y = e z := hez.symm
          _ = 0 := by rw [hz, map_zero]
      have hρnil : ∀ x : N, IsNilpotent (ρ x.1) := by
        intro x
        let a : A := ⟨x.1, hNA x.2⟩
        let xA : NA := ⟨a, x.2⟩
        have hea : e.symm x.1 = (⟨a, 0⟩ : A ⋊⁅ψ⁆ H) := by
          apply e.toLinearEquiv.injective
          calc
            e.toLinearEquiv (e.symm.toLinearEquiv x.1) = x.1 :=
              e.apply_symm_apply x.1
            _ = e.toLinearEquiv (⟨a, 0⟩ : A ⋊⁅ψ⁆ H) := by
              change x.1 = a.1 + 0
              simp [a]
        apply adoDirectSum_isNilpotent ρL σL
        · change IsNilpotent (ρQ (e.symm x.1))
          rw [hea]
          apply adoSemidirectQuotient_left_isNilpotent ψ Q hQ a k
          exact Ideal.pow_mem_pow (hgenN xA) k
        · refine ⟨2, ?_⟩
          rw [pow_two]
          change adoAbelianShear (K := K) (e.symm x.1).right *
            adoAbelianShear (K := K) (e.symm x.1).right = 0
          exact adoAbelianShear_mul_eq_zero _ _
      exact ado_transport_fin_nilpotent_on N ρ hρ hρnil
termination_by Module.finrank K L
decreasing_by exact hfin

/--
**Ado's theorem.** Every finite-dimensional Lie algebra $L$ over a field $K$ of
characteristic zero has a faithful finite-dimensional representation: there are a natural
number $n$ and an injective homomorphism of Lie algebras over $K$ from $L$ into the Lie algebra
of $K$-linear endomorphisms of $K^n$ with the commutator bracket.

Proves `Wanted` entry `ado`.

Proof: Following Tao's 2011 route, the nilpotent and solvable cases are proved by induction using
finite-dimensional quotients of universal enveloping algebras. The general case uses the Levi
decomposition and combines the resulting radical representation with the adjoint representation.

Source: I. D. Ado, Bull. Soc. Phys.-Math. Kazan 7 (1935) and 1947 char-zero theorem; Bourbaki, Lie
Groups and Lie Algebras; Lean states char-zero finite-dimensional version while modern theorem
extends to arbitrary fields.
-/
public theorem ado
    {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
    [Module.Finite K L] :
    ∃ (n : ℕ) (ρ : L →ₗ⁅K⁆ Module.End K (Fin n → K)),
      Function.Injective ρ := by
  classical
  let R : LieIdeal K L := LieAlgebra.radical K L
  let J : LieIdeal K L := adoCommutatorIdeal R
  let _ : LieRing.IsNilpotent J := adoCommutator_isNilpotent R
  let N : LieIdeal K L := J + LieAlgebra.center K L
  let _ : LieRing.IsNilpotent N := adoAdd_center_isNilpotent J
  let NR : LieIdeal K R := N.comap R.incl
  let fNR : NR →ₗ⁅K⁆ N :=
    { toLinearMap :=
        { toFun := fun x => ⟨x.1.1, x.2⟩
          map_add' := by intros; rfl
          map_smul' := by intros; rfl }
      map_lie' := by intros; rfl }
  have hfNR : Function.Injective fNR := by
    intro x y hxy
    exact Subtype.ext (Subtype.ext
      (congrArg (fun z : N => (z.1 : L)) hxy))
  let _ : LieRing.IsNilpotent NR := hfNR.lieAlgebra_isNilpotent
  have hderivedR :
      (LieAlgebra.derivedSeries K R 1 : Submodule K R) ≤ NR.toSubmodule := by
    intro x hx
    change x.1 ∈ N
    have hxmap : R.incl x ∈ (LieAlgebra.derivedSeries K R 1).map R.incl :=
      LieIdeal.mem_map hx
    rw [R.derivedSeries_eq_derivedSeriesOfIdeal_map,
      LieAlgebra.derivedSeriesOfIdeal_succ,
      LieAlgebra.derivedSeriesOfIdeal_zero] at hxmap
    exact Submodule.mem_sup_left (LieSubmodule.mono_lie le_top le_rfl hxmap)
  obtain ⟨m, ρ₀, hρ₀, hnil₀⟩ :=
    adoSolvable_representation NR hderivedR
  let V := Fin m → K
  let _ : LieRingModule R V := LieRingModule.compLieHom V ρ₀
  let _ : LieModule K R V := LieModule.compLieHom V ρ₀
  have hVnil : LieModule.IsNilpotent NR V := by
    rw [LieModule.isNilpotent_iff_forall' (R := K)]
    intro x
    change IsNilpotent (ρ₀ x.1)
    exact hnil₀ x
  obtain ⟨k, hk⟩ := (LieModule.isNilpotent_iff K NR V).mp hVnil
  let b := Module.finBasis K R
  let p (i : Fin (Module.finrank K R)) : Polynomial K :=
    Polynomial.X * (ρ₀ (b i)).charpoly
  let rel (i : Fin (Module.finrank K R)) : adoUEA K R :=
    Polynomial.aeval (UniversalEnvelopingAlgebra.ι K (b i)) (p i)
  let G : Set (adoUEA K R) :=
    Set.range (fun x : NR => UniversalEnvelopingAlgebra.ι K x.1) ∪
      Set.range rel
  let T : Ideal (adoUEA K R) := (TwoSidedIdeal.span G).asIdeal
  let Q : Ideal (adoUEA K R) := T ^ k
  have hgenN (x : NR) : UniversalEnvelopingAlgebra.ι K x.1 ∈ T := by
    exact TwoSidedIdeal.mem_asIdeal.mpr
      (TwoSidedIdeal.subset_span (Set.mem_union_left _ ⟨x, rfl⟩))
  have hgenRel (i : Fin (Module.finrank K R)) : rel i ∈ T := by
    exact TwoSidedIdeal.mem_asIdeal.mpr
      (TwoSidedIdeal.subset_span (Set.mem_union_right _ ⟨i, rfl⟩))
  have hG : ∀ s ∈ G, ∀ j v, v ∈ NR.lcs V j →
      UniversalEnvelopingAlgebra.lift K (LieModule.toEnd K R V) s v ∈
        NR.lcs V (j + 1) := by
    intro s hs
    rcases hs with hs | hs
    · obtain ⟨x, rfl⟩ := hs
      intro j v hv
      rw [UniversalEnvelopingAlgebra.lift_ι_apply]
      change ⁅x.1, v⁆ ∈ NR.lcs V (j + 1)
      rw [LieIdeal.lcs_succ]
      exact LieSubmodule.lie_mem_lie x.2 hv
    · obtain ⟨i, rfl⟩ := hs
      intro j v hv
      have hzero : UniversalEnvelopingAlgebra.lift K
          (LieModule.toEnd K R V) (rel i) = 0 := by
        dsimp [rel]
        rw [← Polynomial.aeval_algHom_apply,
          UniversalEnvelopingAlgebra.lift_ι_apply]
        change Polynomial.aeval (ρ₀ (b i)) (p i) = 0
        simp [p, LinearMap.aeval_self_charpoly]
      rw [hzero, LinearMap.zero_apply]
      exact (NR.lcs V (j + 1)).zero_mem
  have hk' : NR.lcs V k = ⊥ := by
    rw [← LieSubmodule.toSubmodule_inj, LieIdeal.coe_lcs_eq]
    exact congrArg LieSubmodule.toSubmodule hk
  have hQker :
      (Q : Submodule (adoUEA K R) (adoUEA K R)).restrictScalars K ≤
        LinearMap.ker (UniversalEnvelopingAlgebra.lift K ρ₀).toLinearMap := by
    have htoEnd : LieModule.toEnd K R V = ρ₀ := by rfl
    simpa only [Q, T, htoEnd] using
      (adoIdealPower_le_ker_lift NR G hG k hk')
  obtain ⟨C, -, hsum, hinter⟩ :=
    MathlibExt.Algebra.Lie.LandmarkWanted.levi_decomposition (K := K) (L := L)
  have hc : IsCompl R.toSubmodule C.toSubmodule := by
    constructor
    · rw [disjoint_iff]
      exact hinter
    · rw [codisjoint_iff]
      change (LieAlgebra.radical K L).toSubmodule ⊔ C.toSubmodule = ⊤
      simpa only [Submodule.add_eq_sup,
        LieIdeal.toLieSubalgebra_toSubmodule] using hsum
  let ψ : C →ₗ⁅K⁆ LieDerivation K R R := (adoIdealAd R).comp C.incl
  have hT (z : C) : ∀ u, adoExtendDerivation (ψ z) u ∈ T := by
    apply adoUEA_derivation_mem_ideal (adoExtendDerivation (ψ z))
      (adoExtendDerivation_mul (ψ z)) T
    intro a
    rw [adoExtendDerivation_ι]
    have hza : (ψ z a).1 ∈ N := by
      apply Submodule.mem_sup_left
      exact LieSubmodule.lie_mem_lie (LieSubmodule.mem_top z.1) a.2
    exact hgenN ⟨ψ z a, hza⟩
  have hQ : ∀ z u, u ∈ Q → adoExtendDerivation (ψ z) u ∈ Q := by
    intro z u hu
    change adoExtendDerivation (ψ z) u ∈ T ^ k
    exact adoUEA_derivation_preserves_idealPower
      (adoExtendDerivation (ψ z)) (adoExtendDerivation_mul (ψ z))
      T (hT z) k hu
  let B := k * (Module.finrank K V + 1)
  have hp (i : Fin (Module.finrank K R)) : (p i).Monic := by
    exact Polynomial.monic_X.mul (LinearMap.charpoly_monic (ρ₀ (b i)))
  have hdegree (i : Fin (Module.finrank K R)) : (p i ^ k).natDegree = B := by
    rw [(hp i).natDegree_pow]
    simp [p, B, V, LinearMap.charpoly_natDegree,
      (LinearMap.charpoly_monic (ρ₀ (b i))).ne_zero]
  have hpow (i : Fin (Module.finrank K R)) :
      (UniversalEnvelopingAlgebra.ι K (b i)) ^ B ∈ adoModWords Q b B := by
    have hrelpow : Polynomial.aeval
        (UniversalEnvelopingAlgebra.ι K (b i)) (p i ^ k) ∈ Q := by
      rw [map_pow]
      exact Ideal.pow_mem_pow (hgenRel i) k
    have hm := adoAeval_monic_mem_modWords Q b i (p i ^ k)
      ((hp i).pow k) hrelpow
    rwa [hdegree i] at hm
  let qK := (Q : Submodule (adoUEA K R) (adoUEA K R)).restrictScalars K
  let _ : Module.Finite K (adoUEA K R ⧸ qK) :=
    adoQuotient_finite_of_power_relations Q b hpow
  let ρQ : (R ⋊⁅ψ⁆ C) →ₗ⁅K⁆ Module.End K (adoUEA K R ⧸ qK) :=
    adoQuotientRepresentation (adoSemidirectRepresentation ψ) qK
      (adoSemidirectRepresentation_preserves_ideal ψ Q hQ)
  let e : (R ⋊⁅ψ⁆ C) ≃ₗ⁅K⁆ L := adoSemidirectEquivOfIsCompl R C hc
  let ρL : L →ₗ⁅K⁆ Module.End K (adoUEA K R ⧸ qK) := ρQ.comp e.symm
  have hcenter : ∀ x : L, x ∈ LieAlgebra.center K L → ρL x = 0 → x = 0 := by
    intro x hx hxzero
    let r : R := ⟨x, LieAlgebra.center_le_radical K L hx⟩
    have her : e.symm x = (⟨r, 0⟩ : R ⋊⁅ψ⁆ C) := by
      apply e.toLinearEquiv.injective
      calc
        e.toLinearEquiv (e.symm.toLinearEquiv x) = x := e.apply_symm_apply x
        _ = e.toLinearEquiv (⟨r, 0⟩ : R ⋊⁅ψ⁆ C) := by
          change x = r.1 + 0
          simp [r]
    have hr : r = 0 := by
      apply adoSemidirectQuotient_faithful_left ψ ρ₀ hρ₀ Q hQker hQ
      change ρQ ⟨r, 0⟩ = 0
      change ρQ (e.symm x) = 0 at hxzero
      rwa [her] at hxzero
    exact congrArg Subtype.val hr
  exact ado_transport_fin
    (adoDirectSum ρL (LieModule.toEnd K L L))
    (ado_faithful_of_faithful_on_center ρL hcenter)

end MathlibExt.Algebra.Lie.LandmarkWanted
