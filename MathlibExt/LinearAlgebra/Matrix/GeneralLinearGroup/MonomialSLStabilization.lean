/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/
module

public import MathlibExt.GroupTheory.PermutationBilinearTitsStabilization
public import MathlibExt.LinearAlgebra.Matrix.GeneralLinearGroup.Monomial

/-!
# Monomial `SL` successor stabilization over a commutative ring

Reusable ring-generic successor
`MonomialSL R (Fin n) →* MonomialSL R (Fin (n + 1))` obtained by
restricting the accepted `PermutationBilinearTitsStabilization.monomialSuccHom`
on `MonomialBase Rˣ` and using the existing `monomialDetHom_mk` formula
together with `tupleProd_tupleSucc` and `permSuccHom_sign` to preserve the
determinant on the nose.

Matrix realization `monomialSLHom` / `Matrix.SpecialLinearGroup.stabilization`
compatibility is the identified next packet: it requires a block/`reindex`
bridge for `diagonal` and `permMatrix` that is not available as a clean
existing API and would be a substantial new matrix argument. The present
packet intentionally stops at the `MonomialSL` level.
-/

@[expose] public section

open PermutationBilinearTitsStabilization
open PermutationBilinearCocycle
open PermutationBilinearTitsAction

namespace Matrix
namespace GeneralLinearGroup

variable {R : Type*} [CommRing R]
variable {S : Type*} [CommRing S]
variable {n : ℕ}

theorem monomialDetHom_monomialSuccHom (x : MonomialBase Rˣ (Fin n)) :
    monomialDetHom R (Fin (n + 1))
        (monomialSuccHom (A := Rˣ) (n := n) x) =
      monomialDetHom R (Fin n) x := by
  cases x with
  | mk u σ =>
    have h_eq :
        monomialSuccHom (A := Rˣ) (n := n) (⟨u, σ⟩ : MonomialBase Rˣ (Fin n)) =
          (⟨tupleSucc (n := n) u, permSuccHom (n := n) σ⟩ :
            MonomialBase Rˣ (Fin (n + 1))) :=
      rfl
    calc monomialDetHom R (Fin (n + 1))
            (monomialSuccHom (A := Rˣ) (n := n) (⟨u, σ⟩ : MonomialBase Rˣ (Fin n)))
        = monomialDetHom R (Fin (n + 1))
            (⟨tupleSucc (n := n) u, permSuccHom (n := n) σ⟩ :
              MonomialBase Rˣ (Fin (n + 1))) := by rw [h_eq]
      _ = (Finset.univ.prod fun i : Fin (n + 1) => tupleSucc (n := n) u i) *
            Units.map (Int.castRingHom R) (Equiv.Perm.sign (permSuccHom (n := n) σ)) := by
          rw [monomialDetHom_mk]
      _ = (Finset.univ.prod fun i : Fin n => u i) *
            Units.map (Int.castRingHom R) (Equiv.Perm.sign σ) := by
          have h_prod :
              Finset.univ.prod (fun i : Fin (n + 1) => tupleSucc (n := n) u i) =
                Finset.univ.prod (fun i : Fin n => u i) := by
            have ht :
                tupleProd (n := n + 1) (A := Rˣ) (tupleSucc (n := n) u) =
                  tupleProd (n := n) (A := Rˣ) u :=
              tupleProd_tupleSucc (n := n) (A := Rˣ) u
            simpa [tupleProd] using ht
          rw [h_prod, permSuccHom_sign]
      _ = monomialDetHom R (Fin n) (⟨u, σ⟩ : MonomialBase Rˣ (Fin n)) := by
          rw [monomialDetHom_mk]

def monomialSLSuccHom (R : Type*) [CommRing R] {n : ℕ} :
    MonomialSL R (Fin n) →* MonomialSL R (Fin (n + 1)) where
  toFun x :=
    ⟨monomialSuccHom (A := Rˣ) (n := n) (x : MonomialBase Rˣ (Fin n)), by
      have hx : monomialDetHom R (Fin n) (x : MonomialBase Rˣ (Fin n)) = 1 := x.prop
      calc monomialDetHom R (Fin (n + 1))
              (monomialSuccHom (A := Rˣ) (n := n) (x : MonomialBase Rˣ (Fin n)))
          = monomialDetHom R (Fin n) (x : MonomialBase Rˣ (Fin n)) :=
            monomialDetHom_monomialSuccHom (R := R) (n := n) (x : MonomialBase Rˣ (Fin n))
        _ = 1 := hx⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    simp [map_mul]

@[simp]
theorem coe_monomialSLSuccHom (x : MonomialSL R (Fin n)) :
    (monomialSLSuccHom (R := R) (n := n) x : MonomialBase Rˣ (Fin (n + 1))) =
      monomialSuccHom (A := Rˣ) (n := n) (x : MonomialBase Rˣ (Fin n)) :=
  rfl

theorem monomialSLSuccHom_injective {n : ℕ} (R : Type*) [CommRing R] :
    Function.Injective (monomialSLSuccHom (R := R) (n := n)) := by
  intro x y h
  have h_base :
      (monomialSLSuccHom (R := R) (n := n) x : MonomialBase Rˣ (Fin (n + 1))) =
        (monomialSLSuccHom (R := R) (n := n) y : MonomialBase Rˣ (Fin (n + 1))) :=
    congrArg Subtype.val h
  simp only [coe_monomialSLSuccHom] at h_base
  have h_inj := monomialSuccHom_injective (n := n) (A := Rˣ) h_base
  exact Subtype.ext h_inj

theorem monomialSLSuccHom_naturality {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {n : ℕ} :
    (monomialSLSuccHom (R := S) (n := n)).comp (monomialSLMap R S (Fin n) f) =
      (monomialSLMap R S (Fin (n + 1)) f).comp (monomialSLSuccHom (R := R) (n := n)) := by
  apply MonoidHom.ext
  intro x
  apply Subtype.ext
  simp only [MonoidHom.coe_comp, Function.comp_apply, coe_monomialSLMap,
    coe_monomialSLSuccHom]
  have h_nat :=
    monomialSuccHom_naturality (n := n) (A := Rˣ) (A' := Sˣ) (Units.map f)
  have hx :
      ((monomialBaseHom (ι := Fin (n + 1)) (Units.map f)).comp
            (monomialSuccHom (n := n) (A := Rˣ)))
          (x : MonomialBase Rˣ (Fin n)) =
        ((monomialSuccHom (n := n) (A := Sˣ)).comp
            (monomialBaseHom (ι := Fin n) (Units.map f)))
          (x : MonomialBase Rˣ (Fin n)) := by
    exact DFunLike.congr_fun h_nat (x : MonomialBase Rˣ (Fin n))
  exact hx.symm

@[simp]
theorem monomialSLSuccHom_naturality_apply {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) {n : ℕ} (x : MonomialSL R (Fin n)) :
    monomialSLSuccHom (R := S) (monomialSLMap R S (Fin n) f x) =
      monomialSLMap R S (Fin (n + 1)) f (monomialSLSuccHom (R := R) x) :=
  DFunLike.congr_fun (monomialSLSuccHom_naturality (R := R) (S := S) f (n := n)) x

end GeneralLinearGroup
end Matrix
