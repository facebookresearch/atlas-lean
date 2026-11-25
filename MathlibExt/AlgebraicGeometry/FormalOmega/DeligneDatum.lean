/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum.lean`,
`Definitions/Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor.lean` and
`Definitions/Def_CerednikDrinfeld_FormalUpperHalfPlanePoints.lean`
in https://github.com/anthropics/fermats-last-theorem
at commit 6e837e75355538c7f80bab5b956861e86c4eacc2:
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits Mathlib as a whole:
https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.Grassmannian
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import MathlibExt.AlgebraicGeometry.FormalOmega.Lattice

@[expose] public section

noncomputable section

open scoped TensorProduct
open LT.LatticeTree TensorProduct Matrix

namespace CerednikDrinfeld
namespace FormalOmega


section Datum

variable (𝒪 : Type) [CommRing 𝒪] (K : Type) [Field K] [Algebra 𝒪 K] (π : 𝒪)

abbrev latticeBaseChange (B : Type) [CommRing B] [Algebra 𝒪 B] (M : FullLattice 𝒪 K) : Type :=
  B ⊗[𝒪] ↥M.1

variable {𝒪 K}

noncomputable def inclBaseChange (B : Type) [CommRing B] [Algebra 𝒪 B] {M' M : FullLattice 𝒪 K} (h
  : M'.1 ≤ M.1) :
    latticeBaseChange 𝒪 K B M' →ₗ[B] latticeBaseChange 𝒪 K B M :=
  (Submodule.inclusion h).baseChange B

theorem mulVecLinR_injective (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    Function.Injective (mulVecLinR (R := 𝒪) g) := by
  intro v w hvw
  have h := congrArg (fun x => Matrix.mulVec ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix
    (Fin 2) (Fin 2) K) x) hvw
  simpa only [mulVecLinR_apply, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel,
    Units.val_one,
    Matrix.one_mulVec] using h

noncomputable def latticeMapEquiv (g : Matrix.GeneralLinearGroup (Fin 2) K) (M : Submodule 𝒪 (Fin 2
  → K)) :
    ↥M ≃ₗ[𝒪] ↥(latticeMap g M) :=
  Submodule.equivMapOfInjective (mulVecLinR (R := 𝒪) g) (mulVecLinR_injective g) M

def FullLattice.act (g : Matrix.GeneralLinearGroup (Fin 2) K) (M : FullLattice 𝒪 K) : FullLattice 𝒪
  K :=
  ⟨latticeMap g M.1, IsFullLattice.map M.2 g⟩

noncomputable def actBaseChange (B : Type) [CommRing B] [Algebra 𝒪 B] (g :
  Matrix.GeneralLinearGroup (Fin 2) K)
    (M : FullLattice 𝒪 K) : latticeBaseChange 𝒪 K B M ≃ₗ[B] latticeBaseChange 𝒪 K B
      (FullLattice.act g M) :=
  (latticeMapEquiv g M.1).baseChange 𝒪 B _ _

structure DeligneDatum (B : Type) [CommRing B] [Algebra 𝒪 B] : Type where

  line : ∀ M : FullLattice 𝒪 K, Submodule B (latticeBaseChange 𝒪 K B M)

  invertible : ∀ M : FullLattice 𝒪 K, Module.Invertible B (latticeBaseChange 𝒪 K B M ⧸ line M)

  mono : ∀ {M' M : FullLattice 𝒪 K} (h : M'.1 ≤ M.1), (line M').map (inclBaseChange B h) ≤ line M

  homothety : ∀ (c : Kˣ) (M : FullLattice 𝒪 K),
    line (FullLattice.act (scalarGL c) M) = (line M).map (actBaseChange B (scalarGL c)
      M).toLinearMap

  nondeg : ∀ (𝔭 : Ideal B), 𝔭.IsPrime →
    ∃ (M' M : FullLattice 𝒪 K) (_ : M'.1 ≤ M.1),
      (∀ v : ↥M.1, (algebraMap 𝒪 K π) • (v : Fin 2 → K) ∈ M'.1) ∧
      (∀ v : ↥M.1, (v : Fin 2 → K) ∉ M'.1 →
        (1 : B) ⊗ₜ[𝒪] v ∉ line M ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M))) ∧
      (∀ v' : ↥M'.1, (¬ ∃ w : ↥M.1, (v' : Fin 2 → K) = (algebraMap 𝒪 K π) • (w : Fin 2 → K)) →
        (1 : B) ⊗ₜ[𝒪] v' ∉ line M' ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M')))

namespace DeligneDatum

variable {π}
variable {B : Type} [CommRing B] [Algebra 𝒪 B]

theorem ext' {d d' : DeligneDatum (K := K) π B} (h : d.line = d'.line) : d = d' := by
  cases d; cases d'; cases h; rfl

end DeligneDatum

abbrev OmegaObj (B : Type) [CommRing B] [Algebra 𝒪 B] : Type := DeligneDatum (K := K) π B

variable (B : Type) [CommRing B] [Algebra 𝒪 B]

def DeligneDatum.IsPullback (g : Matrix.GeneralLinearGroup (Fin 2) K) (d d' : DeligneDatum (K := K)
  π B) : Prop :=
  ∀ M : FullLattice 𝒪 K, d'.line M = (d.line (FullLattice.act g M)).comap (actBaseChange B g
    M).toLinearMap

variable {B}

noncomputable def lineBaseChange {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B') (M :
  FullLattice 𝒪 K)
    (N : Submodule B (latticeBaseChange 𝒪 K B M)) : Submodule B' (latticeBaseChange 𝒪 K B' M) :=
  Submodule.span B' ((LinearMap.rTensor (↥M.1) f.toLinearMap) '' (N : Set (latticeBaseChange 𝒪 K B
    M)))

def DeligneDatum.IsBaseChange {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B')
    (d : DeligneDatum (K := K) π B) (d' : DeligneDatum (K := K) π B') : Prop :=
  ∀ M : FullLattice 𝒪 K, d'.line M = lineBaseChange f M (d.line M)

end Datum

end FormalOmega
end CerednikDrinfeld

end
