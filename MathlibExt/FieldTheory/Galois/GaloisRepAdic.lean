/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_GaloisRep_Adic.lean`,
`Definitions/Def_GaloisRep_ResidualEquiv.lean`,
`Definitions/Def_GaloisRep_Flat.lean`,
`Definitions/Def_GaloisRep_CompletionBridge.lean`,
`Theorems/Thm_GaloisRepAdic_exists_finiteFlat_padicInt_model_of_isFlatAt.lean`
and
`P2M/Sol/S_GaloisRepAdic_exists_finiteFlat_padicInt_model_of_isFlatAt.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
The completion bridge `padicEmbedding` and `localGaloisToGlobal` and the
subring `Rat.localizedAt` are reused from existing files in this repository,
where they are definitionally the corresponding source carriers.
-/

module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.HopfAlgebra.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import MathlibExt.NumberTheory.Padics.DecompositionSubgroup
public import MathlibExt.RingTheory.DiscreteValuationRing.RatLocalizedAt
public import Mathlib.RingTheory.Bialgebra.Convolution
public import Mathlib.LinearAlgebra.Charpoly.BaseChange
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Trace
public import MathlibExt.FieldTheory.Galois.ResidualGaloisRep
public import MathlibExt.RingTheory.Valuation.InertiaRootsOfUnity
public import MathlibExt.RingTheory.Valuation.LiesOverPrime
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RepresentationTheory.Intertwining
import Mathlib.Algebra.Algebra.Operations
import Mathlib.Algebra.Module.ZMod
import Mathlib.Analysis.Normed.Unbundled.SpectralNorm
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.NumberTheory.Padics.Complex
import Mathlib.RingTheory.Flat.Stability
import Mathlib.RingTheory.HopfAlgebra.TensorProduct
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.RingTheory.Valuation.ValuationSubring

@[expose] public section

universe u v

open scoped TensorProduct

/-- An adic Galois action is continuous when, at every level `n`, it is
trivial modulo the `n`-th power of the maximal ideal on the subgroup fixing
some finite-dimensional intermediate field. -/
public def GaloisActionIsAdicContinuous (A : Type u) [CommRing A] [IsLocalRing A]
    {V : Type v} [AddCommGroup V] [Module A V]
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End A V) :
    Prop :=
  ∀ n : ℕ, ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ),
    FiniteDimensional ℚ L ∧
    ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      (∀ x ∈ L, σ x = x) →
      ∀ v : V, ρ σ v - v ∈
        (IsLocalRing.maximalIdeal A ^ n) • (⊤ : Submodule A V)

/-- A two-dimensional adic Galois representation over a local ring `A`:
a free finite `A`-module of rank two with an adically continuous action of
the absolute Galois group of `ℚ`. -/
public structure GaloisRepAdic (A : Type u) [CommRing A] [IsLocalRing A] :
    Type (max u v + 1) where
  /-- The underlying module. -/
  V : Type v
  [instAddCommGroup : AddCommGroup V]
  [instModule : Module A V]
  [instFree : Module.Free A V]
  [instFinite : Module.Finite A V]
  /-- The representation space is two-dimensional. -/
  finrank_eq : Module.finrank A V = 2
  /-- The Galois action. -/
  ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End A V
  /-- The action is adically continuous. -/
  isAdicContinuous : GaloisActionIsAdicContinuous A ρ

attribute [instance] GaloisRepAdic.instAddCommGroup GaloisRepAdic.instModule
  GaloisRepAdic.instFree GaloisRepAdic.instFinite

namespace GaloisRepAdic

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- The action induced by an adic representation on a quotient level. -/
public noncomputable def levelAction (ρ : GaloisRepAdic A) (I : Ideal A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (ρ.V ⧸ (I • (⊤ : Submodule A ρ.V))) →ₗ[A]
      (ρ.V ⧸ (I • (⊤ : Submodule A ρ.V))) :=
  Submodule.mapQ _ _ (ρ.ρ σ) (by
    rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
    exact Submodule.smul_mono le_rfl le_top)

/-- An adic representation is flat at `p` when every finite quotient level
is the points of a finite flat cocommutative Hopf algebra over the
rationals localized at `p`. -/
public def IsFlatAt (ρ : GaloisRepAdic A) (p : ℕ) : Prop :=
  Finite (IsLocalRing.ResidueField A) ∧ ∀ I : Ideal A, Finite (A ⧸ I) →
    ∃ (H : Type u) (cH : CommRing H) (hH : HopfAlgebra (Rat.localizedAt p) H),
      letI : CommRing H := cH
      letI : HopfAlgebra (Rat.localizedAt p) H := hH
      Module.Finite (Rat.localizedAt p) H ∧
      Module.Flat (Rat.localizedAt p) H ∧
      Coalgebra.IsCocomm (Rat.localizedAt p) H ∧
      ∃ e : WithConv (H →ₐ[Rat.localizedAt p] AlgebraicClosure ℚ) ≃
          (ρ.V ⧸ (I • (⊤ : Submodule A ρ.V))),
        (∀ f g : WithConv (H →ₐ[Rat.localizedAt p] AlgebraicClosure ℚ),
          e (f * g) = e f + e g) ∧
        ∀ (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)
          (f g : WithConv (H →ₐ[Rat.localizedAt p] AlgebraicClosure ℚ)),
          (∀ h : H, g h = σ (f h)) → e g = ρ.levelAction I σ (e f)

end GaloisRepAdic

open scoped Coalgebra.TensorProduct

/-- Convolution of algebra maps evaluated through a representation of the
comultiplication. -/
private theorem algHom_convMul_apply_repr {R C L : Type*} [CommSemiring R] [Semiring C]
    [Bialgebra R C] [CommSemiring L] [Algebra R L] (f g : WithConv (C →ₐ[R] L)) {c : C}
    {ι : Type*} (𝓡 : Coalgebra.Repr R c ι) :
    (f * g) c = ∑ i ∈ 𝓡.index, f (𝓡.left i) * g (𝓡.right i) := by
  rw [AlgHom.convMul_apply, ← 𝓡.eq, map_sum]
  simp only [Algebra.TensorProduct.lift_tmul]

namespace FiniteFlatBaseChange

private theorem norm_cast_le_one (p : ℕ) [Fact p.Prime] (r : Rat.localizedAt p) :
    ‖(algebraMap ℚ ℚ_[p] (r : ℚ))‖ ≤ 1 := by
  obtain ⟨r, hr⟩ := r
  have hden : Nat.Coprime r.den p := hr
  change ‖(algebraMap ℚ ℚ_[p] r)‖ ≤ 1
  have hr' : (algebraMap ℚ ℚ_[p] r) = ((r.num : ℚ_[p]) / (r.den : ℚ_[p])) := by
    rw [eq_ratCast, Rat.cast_def]
  rw [hr', norm_div]
  have hd : ‖(r.den : ℚ_[p])‖ = 1 := (Padic.norm_natCast_eq_one_iff).mpr (Nat.Coprime.symm hden)
  rw [hd, div_one]
  exact Padic.norm_int_le_one r.num

private noncomputable def toPadicInt (p : ℕ) [Fact p.Prime] :
    Rat.localizedAt p →+* ℤ_[p] where
  toFun r := ⟨algebraMap ℚ ℚ_[p] (r : ℚ), norm_cast_le_one p r⟩
  map_one' := by apply Subtype.ext; simp
  map_mul' a b := by
    apply Subtype.ext
    change algebraMap ℚ ℚ_[p] ((a * b : Rat.localizedAt p) : ℚ) =
      algebraMap ℚ ℚ_[p] (a : ℚ) * algebraMap ℚ ℚ_[p] (b : ℚ)
    exact map_mul (algebraMap ℚ ℚ_[p]) (a : ℚ) (b : ℚ)
  map_zero' := by apply Subtype.ext; simp
  map_add' a b := by
    apply Subtype.ext
    change algebraMap ℚ ℚ_[p] ((a + b : Rat.localizedAt p) : ℚ) =
      algebraMap ℚ ℚ_[p] (a : ℚ) + algebraMap ℚ ℚ_[p] (b : ℚ)
    exact map_add (algebraMap ℚ ℚ_[p]) (a : ℚ) (b : ℚ)

@[simp] private theorem coe_toPadicInt (p : ℕ) [Fact p.Prime] (r : Rat.localizedAt p) :
    ((toPadicInt p r : ℤ_[p]) : ℚ_[p]) = algebraMap ℚ ℚ_[p] (r : ℚ) := rfl

open scoped TensorProduct

section points
variable (p : ℕ) [Fact p.Prime]

local notation "Qpb" => PadicAlgCl p

private noncomputable instance algZp : Algebra (Rat.localizedAt p) ℤ_[p] := (toPadicInt p).toAlgebra

private theorem algebraMap_R_Qpb (r : Rat.localizedAt p) :
    algebraMap (Rat.localizedAt p) (PadicAlgCl p) r
      = algebraMap ℚ_[p] (PadicAlgCl p) (algebraMap ℚ ℚ_[p] (r : ℚ)) := by
  have h1 : algebraMap (Rat.localizedAt p) (PadicAlgCl p) r =
      algebraMap ℚ (PadicAlgCl p) (r : ℚ) := rfl
  rw [h1, eq_ratCast, ← map_ratCast (algebraMap ℚ_[p] (PadicAlgCl p)),
    ← eq_ratCast (algebraMap ℚ ℚ_[p])]

private theorem algebraMap_toPadicInt (r : Rat.localizedAt p) :
    algebraMap ℤ_[p] (PadicAlgCl p) (toPadicInt p r) =
      algebraMap (Rat.localizedAt p) (PadicAlgCl p) r := by
  rw [algebraMap_R_Qpb, IsScalarTower.algebraMap_apply ℤ_[p] ℚ_[p] (PadicAlgCl p),
    PadicInt.algebraMap_apply, coe_toPadicInt]

private instance tower : @IsScalarTower (Rat.localizedAt p) ℤ_[p] (PadicAlgCl p)
    Algebra.toSMul Algebra.toSMul Algebra.toSMul := by
  constructor
  intro r z x
  rw [Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc,
    show (algebraMap (Rat.localizedAt p) ℤ_[p]) r = toPadicInt p r from rfl, algebraMap_toPadicInt]

variable (H : Type*) [CommRing H] [HopfAlgebra (Rat.localizedAt p) H]

private noncomputable def ptsBC :
    ((ℤ_[p] ⊗[Rat.localizedAt p] H) →ₐ[ℤ_[p]] PadicAlgCl p) ≃
      (H →ₐ[Rat.localizedAt p] PadicAlgCl p) :=
  { toFun := fun F =>
      (F.restrictScalars (Rat.localizedAt p)).comp Algebra.TensorProduct.includeRight
    invFun := fun g => Algebra.TensorProduct.lift
      (Algebra.ofId ℤ_[p] (PadicAlgCl p)) g (fun _ _ => Commute.all _ _)
    left_inv := fun F => by
      apply Algebra.TensorProduct.ext'
      intro a h
      simp only [Algebra.TensorProduct.lift_tmul, AlgHom.coe_comp, AlgHom.coe_restrictScalars',
        Function.comp_apply, Algebra.TensorProduct.includeRight_apply, Algebra.ofId_apply]
      rw [show a ⊗ₜ[Rat.localizedAt p] h = (a ⊗ₜ 1) * (1 ⊗ₜ h) from by simp, map_mul]
      congr 1
      rw [show (a ⊗ₜ[Rat.localizedAt p] (1 : H)) = algebraMap ℤ_[p] _ a from by
        simp [Algebra.TensorProduct.algebraMap_apply], AlgHom.commutes]
    right_inv := fun g => by
      ext h
      simp }

private noncomputable def reprBC {h : H} {ι𝓡 : Type*}
    (𝓡 : Coalgebra.Repr (Rat.localizedAt p) h ι𝓡) :
    Coalgebra.Repr ℤ_[p] ((1 : ℤ_[p]) ⊗ₜ[Rat.localizedAt p] h) ι𝓡 where
  index := 𝓡.index
  left i := (1 : ℤ_[p]) ⊗ₜ 𝓡.left i
  right i := (1 : ℤ_[p]) ⊗ₜ 𝓡.right i
  eq := by
    rw [TensorProduct.comul_tmul, CommSemiring.comul_apply, ← 𝓡.eq, TensorProduct.tmul_sum, map_sum]
    simp

private theorem ptsBC_mul
    (F G : WithConv ((ℤ_[p] ⊗[Rat.localizedAt p] H) →ₐ[ℤ_[p]] PadicAlgCl p)) :
    ptsBC p H (F * G).ofConv = (WithConv.toConv (ptsBC p H F.ofConv) *
      WithConv.toConv (ptsBC p H G.ofConv)).ofConv := by
  apply AlgHom.ext
  intro h
  let 𝓡 := Coalgebra.Repr.arbitrary (Rat.localizedAt p) h
  change (F * G) ((1 : ℤ_[p]) ⊗ₜ[Rat.localizedAt p] h) =
    (WithConv.toConv (ptsBC p H F.ofConv) * WithConv.toConv (ptsBC p H G.ofConv)) h
  rw [algHom_convMul_apply_repr F G (reprBC p H 𝓡), algHom_convMul_apply_repr _ _ 𝓡]
  exact Finset.sum_congr rfl fun i _ => rfl

end points

end FiniteFlatBaseChange

open Coalgebra

namespace FiniteFlatPoints

variable (p : ℕ) [Fact p.Prime]

local notation "K" => AlgebraicClosure ℚ
local notation "Q" => PadicAlgCl p
local notation "Rp" => Rat.localizedAt p

private noncomputable def embQ : K →ₐ[Rp] Q :=
  { (padicEmbedding p).toRingHom with
    commutes' := fun r => by
      change padicEmbedding p (((r : ℚ) : K)) = ((r : ℚ) : Q)
      exact map_ratCast (padicEmbedding p) (r : ℚ) }

private theorem embQ_apply (x : K) : embQ p x = padicEmbedding p x := rfl

private theorem embQ_injective : Function.Injective (embQ p) := (padicEmbedding p).injective

section pts

variable {p}
variable {H : Type*} [CommRing H] [Algebra (Rat.localizedAt p) H]
  [Module.Finite (Rat.localizedAt p) H]

private theorem exists_embQ_eq_apply (φ : H →ₐ[Rp] Q) (h : H) : ∃ y : K, embQ p y = φ h := by
  have hint : IsIntegral Rp h := Algebra.IsIntegral.isIntegral h
  obtain ⟨P, hPmonic, hPeval⟩ := hint
  have hP0 : P ≠ 0 := hPmonic.ne_zero
  have hroot : (P.map (algebraMap Rp Q)).IsRoot (φ h) := by
    rw [Polynomial.IsRoot.def, Polynomial.eval_map, ← Polynomial.aeval_def,
      Polynomial.aeval_algHom_apply,
      Polynomial.aeval_def, hPeval, map_zero]
  set g : Polynomial K := P.map (algebraMap Rp K) with hg
  have hsplit : g.Splits := IsAlgClosed.splits g
  have hroots := hsplit.roots_map (embQ p).toRingHom
  have hgmap : g.map (embQ p).toRingHom = P.map (algebraMap Rp Q) := by
    rw [hg, Polynomial.map_map]
    congr 1
    ext r
    exact (embQ p).commutes r
  have hmem : φ h ∈ (g.map (embQ p).toRingHom).roots := by
    rw [hgmap, Polynomial.mem_roots (Polynomial.map_monic_ne_zero hPmonic)]
    exact hroot
  rw [hroots, Multiset.mem_map] at hmem
  obtain ⟨y, -, hy⟩ := hmem
  exact ⟨y, hy⟩

private noncomputable def lift (φ : H →ₐ[Rp] Q) : H →ₐ[Rp] K where
  toFun h := (exists_embQ_eq_apply φ h).choose
  map_one' := embQ_injective p (by rw [(exists_embQ_eq_apply φ 1).choose_spec, map_one, map_one])
  map_mul' a b := embQ_injective p (by
    rw [(exists_embQ_eq_apply φ (a * b)).choose_spec, map_mul, map_mul,
      (exists_embQ_eq_apply φ a).choose_spec, (exists_embQ_eq_apply φ b).choose_spec])
  map_zero' := embQ_injective p (by rw [(exists_embQ_eq_apply φ 0).choose_spec, map_zero, map_zero])
  map_add' a b := embQ_injective p (by
    rw [(exists_embQ_eq_apply φ (a + b)).choose_spec, map_add, map_add,
      (exists_embQ_eq_apply φ a).choose_spec, (exists_embQ_eq_apply φ b).choose_spec])
  commutes' r := embQ_injective p (by
    rw [(exists_embQ_eq_apply φ (algebraMap Rp H r)).choose_spec, AlgHom.commutes, AlgHom.commutes])

private theorem embQ_lift (φ : H →ₐ[Rp] Q) (h : H) : embQ p (lift φ h) = φ h :=
  (exists_embQ_eq_apply φ h).choose_spec

private theorem embQ_comp_lift (φ : H →ₐ[Rp] Q) : (embQ p).comp (lift φ) = φ :=
  AlgHom.ext fun h => embQ_lift φ h

private theorem lift_embQ_comp (ψ : H →ₐ[Rp] K) : lift ((embQ p).comp ψ) = ψ :=
  AlgHom.ext fun h => embQ_injective p (by rw [embQ_lift]; rfl)

private noncomputable def ptsQbar : WithConv (H →ₐ[Rp] Q) ≃ WithConv (H →ₐ[Rp] K) where
  toFun F := WithConv.toConv (lift (WithConv.ofConv F))
  invFun f := WithConv.toConv ((embQ p).comp (WithConv.ofConv f))
  left_inv F := by simp [embQ_comp_lift]
  right_inv f := by simp [lift_embQ_comp]

private theorem embQ_ptsQbar_apply (F : WithConv (H →ₐ[Rp] Q)) (h : H) :
    embQ p (ptsQbar F h) = F h :=
  embQ_lift _ h

private theorem ptsQbar_symm_apply (f : WithConv (H →ₐ[Rp] K)) (h : H) :
    ptsQbar.symm f h = embQ p (f h) := rfl

private theorem ptsQbar_apply_of_forall_eq (τ : Q ≃ₐ[ℚ_[p]] Q) (F G : WithConv (H →ₐ[Rp] Q))
    (hFG : ∀ h : H, G h = τ (F h)) (h : H) :
    ptsQbar G h = localGaloisToGlobal p τ (ptsQbar F h) := by
  apply embQ_injective p
  rw [embQ_ptsQbar_apply, hFG, embQ_apply, padicEmbedding_localGaloisToGlobal, ← embQ_apply,
    embQ_ptsQbar_apply]

end pts

section hopf

variable {p}
variable {H : Type*} [CommRing H] [HopfAlgebra (Rat.localizedAt p) H]
  [Module.Finite (Rat.localizedAt p) H]

private theorem ptsQbar_symm_mul (f g : WithConv (H →ₐ[Rp] K)) :
    (ptsQbar.symm (f * g) : WithConv (H →ₐ[Rp] Q)) = ptsQbar.symm f * ptsQbar.symm g := by
  classical
  have hext : ∀ (F G : WithConv (H →ₐ[Rp] Q)), (∀ h : H, F h = G h) → F = G := by
    intro F G hFG
    have : WithConv.ofConv F = WithConv.ofConv G := AlgHom.ext hFG
    simpa using congrArg WithConv.toConv this
  apply hext
  intro h
  let 𝓡 := Coalgebra.Repr.arbitrary Rp h
  rw [ptsQbar_symm_apply, algHom_convMul_apply_repr f g 𝓡,
    algHom_convMul_apply_repr _ _ 𝓡, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, ptsQbar_symm_apply, ptsQbar_symm_apply]

private theorem ptsQbar_mul (F G : WithConv (H →ₐ[Rp] Q)) :
    (ptsQbar (F * G) : WithConv (H →ₐ[Rp] K)) = ptsQbar F * ptsQbar G := by
  apply ptsQbar.symm.injective
  rw [Equiv.symm_apply_apply, ptsQbar_symm_mul, Equiv.symm_apply_apply, Equiv.symm_apply_apply]

end hopf

section bot

variable {p}
variable {A : Type u} [CommRing A] [IsLocalRing A]

omit [Fact p.Prime] in
private theorem exists_model_of_isFlatAt [Finite A] (ρ : GaloisRepAdic A)
    (hρ : ρ.IsFlatAt p) :
    ∃ (H : Type u) (cH : CommRing H) (hH : HopfAlgebra Rp H),
      letI : CommRing H := cH
      letI : HopfAlgebra Rp H := hH
      Module.Finite Rp H ∧ Module.Flat Rp H ∧ Coalgebra.IsCocomm Rp H ∧
      ∃ e : WithConv (H →ₐ[Rp] K) ≃ ρ.V,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : K ≃ₐ[ℚ] K) (f g : WithConv (H →ₐ[Rp] K)),
          (∀ h : H, g h = σ (f h)) → e g = ρ.ρ σ (e f) := by
  obtain ⟨-, hflat⟩ := hρ
  have : Finite (A ⧸ (⊥ : Ideal A)) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
  obtain ⟨H, cH, hH, hfin, hfl, hcc, e, he_add, he_act⟩ := hflat ⊥ inferInstance
  have hbot : ((⊥ : Ideal A) • (⊤ : Submodule A ρ.V)) = ⊥ := Submodule.bot_smul _
  let q : (ρ.V ⧸ ((⊥ : Ideal A) • (⊤ : Submodule A ρ.V))) ≃ₗ[A] ρ.V :=
    Submodule.quotEquivOfEqBot _ hbot
  refine ⟨H, cH, hH, hfin, hfl, hcc, e.trans q.toEquiv, ?_, ?_⟩
  · intro f g
    change q (e (f * g)) = q (e f) + q (e g)
    rw [he_add, map_add]
  · intro σ f g hfg
    change q (e g) = ρ.ρ σ (q (e f))
    rw [he_act σ f g hfg]
    obtain ⟨v, hv⟩ := Submodule.Quotient.mk_surjective _ (e f)
    rw [← hv]
    rfl

end bot

end FiniteFlatPoints


public theorem GaloisRepAdic.exists_finiteFlat_padicInt_model_of_isFlatAt
    {A : Type u} [CommRing A] [IsLocalRing A] [Finite A] (p : ℕ) [Fact p.Prime]
    (ρ : GaloisRepAdic A) (hρ : ρ.IsFlatAt p) :
    ∃ (H : Type u) (cH : CommRing H) (hH : HopfAlgebra ℤ_[p] H),
      letI : CommRing H := cH
      letI : HopfAlgebra ℤ_[p] H := hH
      Module.Finite ℤ_[p] H ∧ Module.Flat ℤ_[p] H ∧ Coalgebra.IsCocomm ℤ_[p] H ∧
      ∃ e : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ρ.V,
        (∀ f g, e (f * g) = e f + e g) ∧
        ∀ (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
          (f g : WithConv (H →ₐ[ℤ_[p]] PadicAlgCl p)),
          (∀ h : H, g h = σ (f h)) → e g = ρ.ρ (localGaloisToGlobal p σ) (e f) := by
  classical
  obtain ⟨H0, i1, i2, hfin, hfl, hcc, e0, he0_add, he0_act⟩ :=
    FiniteFlatPoints.exists_model_of_isFlatAt (p := p) ρ hρ
  have := hfin; have := hfl; have := hcc
  let HB := ℤ_[p] ⊗[Rat.localizedAt p] H0
  let E : WithConv (HB →ₐ[ℤ_[p]] PadicAlgCl p) ≃ ρ.V :=
    (((Equiv.mk WithConv.ofConv WithConv.toConv (fun _ => rfl) (fun _ => rfl)).trans
      (FiniteFlatBaseChange.ptsBC p H0)).trans
      (Equiv.mk WithConv.toConv WithConv.ofConv (fun _ => rfl) (fun _ => rfl))).trans
      (FiniteFlatPoints.ptsQbar.trans e0)
  have hE : ∀ F : WithConv (HB →ₐ[ℤ_[p]] PadicAlgCl p),
      E F = e0 (FiniteFlatPoints.ptsQbar (WithConv.toConv
        (FiniteFlatBaseChange.ptsBC p H0 (WithConv.ofConv F)))) := fun _ => rfl
  refine ⟨HB, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, E, ?_, ?_⟩
  · intro F G
    rw [hE, hE, hE, FiniteFlatBaseChange.ptsBC_mul, WithConv.toConv_ofConv,
      FiniteFlatPoints.ptsQbar_mul, he0_add]
  · intro σ F G hFG
    rw [hE, hE]
    apply he0_act
    intro h
    apply FiniteFlatPoints.ptsQbar_apply_of_forall_eq σ
    intro h'
    exact hFG ((1 : ℤ_[p]) ⊗ₜ[Rat.localizedAt p] h')

namespace ResidualGaloisRep

variable {k : Type u} [Field k]

/-- An equivalence of residual Galois representations: an equivalence of the
underlying representations of the absolute Galois group of `ℚ`, with the
standard `refl`, `symm` and `trans` of `Representation.Equiv`. -/
public abbrev Equiv (ρ₁ ρ₂ : ResidualGaloisRep k) : Type _ :=
  Representation.Equiv ρ₁.ρ ρ₂.ρ

/-- Two residual Galois representations are equivalent when there is an
equivalence between them. -/
public def IsEquiv (ρ₁ ρ₂ : ResidualGaloisRep k) : Prop :=
  Nonempty (Equiv ρ₁ ρ₂)

end ResidualGaloisRep

namespace GaloisRepAdic

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- An adic Galois representation is unramified at `q` when every element
of an inertia subgroup over `q` acts trivially. -/
public def IsUnramifiedAt (ρ : GaloisRepAdic A) (q : ℕ) : Prop :=
  ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
    ∀ σ ∈ P.inertiaSubgroupIn ℚ, ρ.ρ σ = 1

/-- The determinant of an adic Galois representation, as a character with
values in the units of the coefficient ring. -/
public noncomputable def det (ρ : GaloisRepAdic A) :
    (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Aˣ :=
  (LinearMap.det.comp ρ.ρ).toHomUnits

/-- The determinant is the unit attached to the linear determinant. -/
theorem det_apply (ρ : GaloisRepAdic A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (ρ.det σ : A) = LinearMap.det (ρ.ρ σ) :=
  rfl

/-- The trace of a Galois element in an adic Galois representation. -/
public noncomputable def trace (ρ : GaloisRepAdic A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : A :=
  LinearMap.trace A ρ.V (ρ.ρ σ)

/-- The trace is the linear trace of the representing endomorphism. -/
theorem trace_def (ρ : GaloisRepAdic A)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ρ.trace σ = LinearMap.trace A ρ.V (ρ.ρ σ) :=
  rfl

/-- Base change of an adic Galois representation along a local ring
homomorphism. -/
public noncomputable def baseChangeAlong {B : Type v} [CommRing B]
    [IsLocalRing B] (φ : A →+* B) (hφ : IsLocalHom φ)
    (ρ : GaloisRepAdic A) : GaloisRepAdic B :=
  letI : Algebra A B := φ.toAlgebra
  { V := B ⊗[A] ρ.V
    finrank_eq := by rw [Module.finrank_baseChange, ρ.finrank_eq]
    ρ := { toFun := fun σ => (ρ.ρ σ).baseChange B
           map_one' := by rw [map_one, LinearMap.baseChange_one]
           map_mul' := fun σ τ => by rw [map_mul, LinearMap.baseChange_mul] }
    isAdicContinuous := by
      intro n
      obtain ⟨L, hL, h1⟩ := ρ.isAdicContinuous n
      refine ⟨L, hL, fun σ hσ => ?_⟩
      have hmap : (IsLocalRing.maximalIdeal A ^ n).map φ ≤
          IsLocalRing.maximalIdeal B ^ n := by
        rw [Ideal.map_pow]
        exact Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr fun a ha =>
          Ideal.mem_comap.mpr (haveI := hφ; map_nonunit φ a ha)) n
      have hpure : ∀ (b : B) (v : ρ.V),
          (ρ.ρ σ).baseChange B (b ⊗ₜ[A] v) - b ⊗ₜ[A] v ∈
            (IsLocalRing.maximalIdeal B ^ n) • (⊤ : Submodule B (B ⊗[A] ρ.V)) := by
        intro b v
        rw [LinearMap.baseChange_tmul, ← TensorProduct.tmul_sub]
        refine Submodule.smul_induction_on (p := fun x => b ⊗ₜ[A] x ∈
          (IsLocalRing.maximalIdeal B ^ n) • (⊤ : Submodule B (B ⊗[A] ρ.V)))
          (h1 σ hσ v) ?_ ?_
        · intro a ha w _
          rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def,
            ← smul_eq_mul, ← TensorProduct.smul_tmul']
          exact Submodule.smul_mem_smul (hmap (Ideal.mem_map_of_mem φ ha))
            Submodule.mem_top
        · intro x y hx hy
          rw [TensorProduct.tmul_add]
          exact Submodule.add_mem _ hx hy
      intro w
      induction w using TensorProduct.induction_on with
      | zero => rw [map_zero, sub_zero]; exact Submodule.zero_mem _
      | tmul b v => exact hpure b v
      | add x y hx hy =>
        rw [map_add, add_sub_add_comm]
        exact Submodule.add_mem _ hx hy }

/-- The residual representation of an adic Galois representation, obtained
by base change to the residue field. -/
public noncomputable def residual (ρ : GaloisRepAdic A) :
    ResidualGaloisRep (IsLocalRing.ResidueField A) :=
  { V := IsLocalRing.ResidueField A ⊗[A] ρ.V
    finrank_eq := by rw [Module.finrank_baseChange, ρ.finrank_eq]
    ρ := { toFun := fun σ => (ρ.ρ σ).baseChange (IsLocalRing.ResidueField A)
           map_one' := by rw [map_one, LinearMap.baseChange_one]
           map_mul' := fun σ τ => by rw [map_mul, LinearMap.baseChange_mul] }
    factorsThroughFiniteLevel := by
      obtain ⟨L, hL, h1⟩ := ρ.isAdicContinuous 1
      refine ⟨L, hL, fun σ hσ => ?_⟩
      have hkill : ∀ x ∈ (IsLocalRing.maximalIdeal A ^ 1) • (⊤ : Submodule A ρ.V),
          ∀ c : IsLocalRing.ResidueField A, c ⊗ₜ[A] x = 0 := by
        intro x hx c
        refine Submodule.smul_induction_on
          (p := fun x => c ⊗ₜ[A] x = (0 : IsLocalRing.ResidueField A ⊗[A] ρ.V))
          hx ?_ ?_
        · intro a ha w _
          rw [pow_one] at ha
          rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def,
            IsLocalRing.ResidueField.algebraMap_eq,
            (IsLocalRing.residue_eq_zero_iff a).mpr ha, zero_mul,
            TensorProduct.zero_tmul]
        · intro x y hx hy
          rw [TensorProduct.tmul_add, hx, hy, add_zero]
      refine LinearMap.ext fun w => ?_
      rw [MonoidHom.coe_mk, OneHom.coe_mk]
      induction w using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero]
      | tmul c v =>
        rw [LinearMap.baseChange_tmul, Module.End.one_apply, ← sub_eq_zero,
          ← TensorProduct.tmul_sub]
        exact hkill _ (h1 σ hσ v) c
      | add x y hx hy => rw [map_add, map_add, hx, hy] }

/-- An equivalence of adic Galois representations: an equivalence of the
underlying representations of the absolute Galois group of `ℚ`, with the
standard `refl`, `symm` and `trans` of `Representation.Equiv`. -/
public abbrev Equiv (ρ₁ ρ₂ : GaloisRepAdic A) : Type _ :=
  Representation.Equiv ρ₁.ρ ρ₂.ρ

/-- Two adic Galois representations are equivalent when there is an
equivalence between them. -/
public def IsEquiv (ρ₁ ρ₂ : GaloisRepAdic A) : Prop :=
  Nonempty (Equiv ρ₁ ρ₂)

namespace Equiv

/-- Base change of an equivalence of adic Galois representations. -/
public noncomputable def baseChangeAlong {B : Type v} [CommRing B]
    [IsLocalRing B] (φ : A →+* B) (hφ : IsLocalHom φ)
    {ρ₁ ρ₂ : GaloisRepAdic A} (e : Equiv ρ₁ ρ₂) :
    Equiv (ρ₁.baseChangeAlong φ hφ) (ρ₂.baseChangeAlong φ hφ) :=
  letI : Algebra A B := φ.toAlgebra
  .mk (e.toLinearEquiv.baseChange A B ρ₁.V ρ₂.V) fun σ => LinearMap.ext fun x => by
    show e.toLinearEquiv.baseChange A B ρ₁.V ρ₂.V ((ρ₁.ρ σ).baseChange B x) =
      (ρ₂.ρ σ).baseChange B (e.toLinearEquiv.baseChange A B ρ₁.V ρ₂.V x)
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul b v =>
      rw [LinearMap.baseChange_tmul, LinearEquiv.baseChange_tmul,
        LinearEquiv.baseChange_tmul, LinearMap.baseChange_tmul]
      exact congrArg (b ⊗ₜ[A] ·) (e.toIntertwiningMap.isIntertwining _ _ σ v)
    | add x y hx hy => simp only [map_add, hx, hy]

/-- The residual equivalence induced by an equivalence of adic Galois
representations. -/
public noncomputable def residual {ρ₁ ρ₂ : GaloisRepAdic A}
    (e : Equiv ρ₁ ρ₂) :
    ResidualGaloisRep.Equiv ρ₁.residual ρ₂.residual :=
  .mk (e.toLinearEquiv.baseChange A (IsLocalRing.ResidueField A) ρ₁.V ρ₂.V)
    fun σ => LinearMap.ext fun x => by
      show e.toLinearEquiv.baseChange A (IsLocalRing.ResidueField A) ρ₁.V ρ₂.V
          ((ρ₁.ρ σ).baseChange (IsLocalRing.ResidueField A) x) =
        (ρ₂.ρ σ).baseChange (IsLocalRing.ResidueField A)
          (e.toLinearEquiv.baseChange A (IsLocalRing.ResidueField A) ρ₁.V ρ₂.V x)
      induction x using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul b v =>
        rw [LinearMap.baseChange_tmul, LinearEquiv.baseChange_tmul,
          LinearEquiv.baseChange_tmul, LinearMap.baseChange_tmul]
        exact congrArg (b ⊗ₜ[A] ·) (e.toIntertwiningMap.isIntertwining _ _ σ v)
      | add x y hx hy => simp only [map_add, hx, hy]

end Equiv

/-- The residual representation underlying an adic representation over a
field, viewed as an adic representation itself. -/
public def toResidualGaloisRep {k : Type u} [Field k] (ρ : GaloisRepAdic k) :
    ResidualGaloisRep k :=
  { V := ρ.V
    finrank_eq := ρ.finrank_eq
    ρ := ρ.ρ
    factorsThroughFiniteLevel := by
      obtain ⟨L, hL, h1⟩ := ρ.isAdicContinuous 1
      refine ⟨L, hL, fun σ hσ => LinearMap.ext fun v => ?_⟩
      have hbot : IsLocalRing.maximalIdeal k = ⊥ :=
        (Ideal.eq_bot_or_top _).resolve_right
          (Ideal.IsMaximal.ne_top inferInstance)
      have h := h1 σ hσ v
      rw [hbot, pow_one, Submodule.bot_smul, Submodule.mem_bot, sub_eq_zero] at h
      exact h }

/-- An adic Galois representation over a field obtained from a residual
Galois representation. -/
public def ofResidualGaloisRep {k : Type u} [Field k]
    (ρ : ResidualGaloisRep k) : GaloisRepAdic k :=
  { V := ρ.V
    finrank_eq := ρ.finrank_eq
    ρ := ρ.ρ
    isAdicContinuous := by
      intro n
      obtain ⟨L, hL, h1⟩ := ρ.factorsThroughFiniteLevel
      refine ⟨L, hL, fun σ hσ v => ?_⟩
      rw [h1 σ hσ, Module.End.one_apply, sub_self]
      exact Submodule.zero_mem _ }

end GaloisRepAdic
