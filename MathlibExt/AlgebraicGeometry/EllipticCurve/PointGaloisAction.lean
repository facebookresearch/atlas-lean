/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_FLTPrelim_GaloisRep.lean`
and
`Definitions/Def_EllipticCurve_FrobeniusTrace.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers
of the Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a
proof-extraction framework; the statements and proofs are reused
here with that machinery removed and the names restated in
Mathlib style.

`Definitions/Def_FLTPrelim_GaloisRep.lean` carries its own header:
Copyright (c) 2024 Imperial College London FLT project contributors.
Released under Apache 2.0 license.
Adapted from the Imperial College London FLT formalization
(https://github.com/ImperialCollegeLondon/FLT).
-/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.RepresentationTheory.Irreducible

@[expose] public section

open scoped WeierstrassCurve.Affine

universe r s v

namespace WeierstrassCurve.Affine.Point

variable {R : Type r} {S : Type s} {K : Type v} [CommRing R]
  [CommRing S] [Field K] [DecidableEq K] {W' : Affine R}
  [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K]

/-- Galois automorphisms act on points by applying the automorphism
to the coordinates. -/
noncomputable instance instSMulAlgEquiv :
    SMul (K ≃ₐ[S] K) (W'⁄K).Point :=
  ⟨fun σ P => Point.map σ.toAlgHom P⟩

theorem algEquiv_smul_def (σ : K ≃ₐ[S] K) (P : (W'⁄K).Point) :
    σ • P = Point.map σ.toAlgHom P :=
  rfl

/-- The coordinate action of Galois automorphisms on points is a
distributive multiplicative action. -/
noncomputable instance instDistribMulActionAlgEquiv :
    DistribMulAction (K ≃ₐ[S] K) (W'⁄K).Point where
  one_smul P := by cases P <;> rfl
  mul_smul σ τ P := by cases P <;> rfl
  smul_zero _ := rfl
  smul_add σ P Q := (Point.map σ.toAlgHom).map_add P Q

theorem algEquiv_smul_zsmul (σ : K ≃ₐ[S] K) (m : ℤ)
    (P : (W'⁄K).Point) : σ • (m • P) = m • (σ • P) :=
  (Point.map σ.toAlgHom).map_zsmul m P

theorem smul_mem_torsionBy {n : ℕ} (σ : K ≃ₐ[S] K)
    {P : (W'⁄K).Point}
    (hP : P ∈ Submodule.torsionBy ℤ (W'⁄K).Point n) :
    σ • P ∈ Submodule.torsionBy ℤ (W'⁄K).Point n := by
  rw [Submodule.mem_torsionBy_iff] at hP ⊢
  rw [← algEquiv_smul_zsmul, hP, smul_zero]

/-- Galois automorphisms act on the `n`-torsion submodule. -/
noncomputable instance instSMulTorsionBy (n : ℕ) :
    SMul (K ≃ₐ[S] K) (Submodule.torsionBy ℤ (W'⁄K).Point n) :=
  ⟨fun σ P => ⟨σ • (P : (W'⁄K).Point), smul_mem_torsionBy σ P.2⟩⟩

/-- The action on the `n`-torsion submodule is distributive. -/
noncomputable instance instDistribMulActionTorsionBy (n : ℕ) :
    DistribMulAction (K ≃ₐ[S] K)
      (Submodule.torsionBy ℤ (W'⁄K).Point n) where
  one_smul P := Subtype.ext <| one_smul _ (P : (W'⁄K).Point)
  mul_smul σ τ P := Subtype.ext <| mul_smul σ τ (P : (W'⁄K).Point)
  smul_zero σ := Subtype.ext <| smul_zero (A := (W'⁄K).Point) σ
  smul_add σ P Q :=
    Subtype.ext <| smul_add σ (P : (W'⁄K).Point) (Q : (W'⁄K).Point)

/-- The `n`-torsion submodule is a module over `ZMod n`. -/
noncomputable instance instModuleZModTorsionBy (n : ℕ) :
    Module (ZMod n) (Submodule.torsionBy ℤ (W'⁄K).Point n) :=
  AddCommGroup.zmodModule fun x => by
    rw [← Nat.cast_smul_eq_nsmul ℤ n x]
    exact Submodule.smul_torsionBy _ x

/-- The Galois action and scalar multiplication on torsion
commute. -/
instance instSMulCommClassAlgEquivZModTorsionBy (n : ℕ) :
    SMulCommClass (K ≃ₐ[S] K) (ZMod n)
      (Submodule.torsionBy ℤ (W'⁄K).Point n) where
  smul_comm σ c x :=
    ZMod.map_smul
      (DistribSMul.toAddMonoidHom
        (Submodule.torsionBy ℤ (W'⁄K).Point n) σ) c x

variable (S) in
/-- The Galois representation on `n`-torsion, as module
endomorphisms. -/
noncomputable def galoisRepModuleEnd (W' : Affine R) (n : ℕ) :
    Representation (ZMod n) (K ≃ₐ[S] K)
      (Submodule.torsionBy ℤ (W'⁄K).Point n) :=
  DistribMulAction.toModuleEnd (ZMod n)
    (Submodule.torsionBy ℤ (W'⁄K).Point n)

/-- The endomorphism attached to `σ` acts as `σ` does on points. -/
@[simp] theorem galoisRepModuleEnd_apply (W' : Affine R) (n : ℕ)
    (σ : K ≃ₐ[S] K)
    (x : Submodule.torsionBy ℤ (W'⁄K).Point n) :
    galoisRepModuleEnd S W' n σ x = σ • x :=
  rfl

variable (S) in
/-- The Galois representation on `n`-torsion is irreducible: its
subrepresentations form a simple order, so the `n`-torsion is
nontrivial and its only Galois-stable submodules are `⊥` and `⊤`
(`galoisRepIsIrreducible_iff`).

This is the body of `Representation.IsIrreducible`, which Mathlib
states only over a field; for prime `n` the two agree
(`galoisRepIsIrreducible_iff_isIrreducible`). -/
public abbrev GaloisRepIsIrreducible (W' : Affine R) (n : ℕ) : Prop :=
  IsSimpleOrder (Subrepresentation (galoisRepModuleEnd (K := K) S W' n))

/-- For prime `n`, irreducibility of the Galois representation on
`n`-torsion is Mathlib's `Representation.IsIrreducible`. -/
theorem galoisRepIsIrreducible_iff_isIrreducible (W' : Affine R)
    (n : ℕ) [Fact n.Prime] :
    GaloisRepIsIrreducible (K := K) S W' n ↔
      Representation.IsIrreducible (k := ZMod n) (G := K ≃ₐ[S] K)
        (V := Submodule.torsionBy ℤ (W'⁄K).Point n)
        (galoisRepModuleEnd (K := K) S W' n) :=
  Iff.rfl

/-- Irreducibility unfolded: the `n`-torsion is nontrivial and every
submodule stable under all Galois automorphisms is `⊥` or `⊤`. -/
theorem galoisRepIsIrreducible_iff (W' : Affine R) (n : ℕ) :
    GaloisRepIsIrreducible (K := K) S W' n ↔
      Nontrivial (Submodule.torsionBy ℤ (W'⁄K).Point n) ∧
        ∀ N : Submodule (ZMod n)
            (Submodule.torsionBy ℤ (W'⁄K).Point n),
          (∀ σ : K ≃ₐ[S] K, ∀ x ∈ N, σ • x ∈ N) → N = ⊥ ∨ N = ⊤ := by
  constructor
  · intro h
    refine ⟨?_, fun N hN => ?_⟩
    · by_contra hV
      rw [not_nontrivial_iff_subsingleton] at hV
      have := (Submodule.subsingleton_iff (ZMod n)).mpr hV
      exact bot_ne_top
        (Subrepresentation.toSubmodule_injective (Subsingleton.elim
          (⊥ : Subrepresentation (galoisRepModuleEnd (K := K) S W' n)).toSubmodule
          (⊤ : Subrepresentation (galoisRepModuleEnd (K := K) S W' n)).toSubmodule))
    · rcases h.eq_bot_or_eq_top ⟨N, fun σ x hx => hN σ x hx⟩ with h' | h'
      · exact Or.inl (congrArg Subrepresentation.toSubmodule h')
      · exact Or.inr (congrArg Subrepresentation.toSubmodule h')
  · rintro ⟨hV, hN⟩
    have : Nontrivial
        (Subrepresentation (galoisRepModuleEnd (K := K) S W' n)) :=
      ⟨⊥, ⊤, fun h => bot_ne_top (congrArg Subrepresentation.toSubmodule h)⟩
    refine ⟨fun N => ?_⟩
    rcases hN N.toSubmodule (fun σ x hx => N.apply_mem_toSubmodule σ hx)
      with h | h
    · exact Or.inl (Subrepresentation.toSubmodule_injective h)
    · exact Or.inr (Subrepresentation.toSubmodule_injective h)

end WeierstrassCurve.Affine.Point
