/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_CerednikDrinfeld_FormalUpperHalfPlaneChartRings.lean`,
`Definitions/Def_CerednikDrinfeld_FormalUpperHalfPlaneCharts.lean`,
`Definitions/Def_CerednikDrinfeld_FormalUpperHalfPlaneDatum.lean`
and `Definitions/Def_LatticeTreeOrbital.lean`
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
-/

module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.PicardGroup

@[expose] public section

open scoped TensorProduct Matrix

namespace LT.LatticeTree

variable (R : Type*) [CommRing R] (K : Type*) [Field K] [Algebra R K]

def stdLattice : Submodule R (Fin 2 → K) where
  carrier := {v | ∀ i, IsLocalization.IsInteger R (v i)}
  add_mem' := fun hv hw i => IsLocalization.isInteger_add (hv i) (hw i)
  zero_mem' := fun _ => IsLocalization.isInteger_zero
  smul_mem' := fun r v hv i => by
    rw [Pi.smul_apply]
    exact IsLocalization.isInteger_smul (hv i)

theorem mem_stdLattice {v : Fin 2 → K} :
    v ∈ stdLattice R K ↔ ∀ i, IsLocalization.IsInteger R (v i) := Iff.rfl

attribute [local simp] mem_stdLattice
theorem single_one_mem_stdLattice (j : Fin 2) :
    (Pi.single j 1 : Fin 2 → K) ∈ stdLattice R K := by
  intro i
  rcases eq_or_ne i j with rfl | h
  · rw [Pi.single_eq_same]
    exact IsLocalization.isInteger_one
  · rw [Pi.single_eq_of_ne h]
    exact IsLocalization.isInteger_zero

theorem stdLattice_eq_span :
    stdLattice R K = Submodule.span R (Set.range fun j => (Pi.single j 1 : Fin 2 → K)) := by
  apply le_antisymm
  · intro v hv
    choose w hw using hv
    have hv' : v = w 0 • (Pi.single 0 1 : Fin 2 → K) + w 1 • (Pi.single 1 1 : Fin 2 → K) := by
      funext i
      have h0 : algebraMap R K (w 0) = v 0 := hw 0
      have h1 : algebraMap R K (w 1) = v 1 := hw 1
      fin_cases i <;>
        simp [Algebra.smul_def, ← h0, ← h1]
    rw [hv']
    exact add_mem
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨1, rfl⟩))
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact single_one_mem_stdLattice R K j

theorem stdLattice_fg : (stdLattice R K).FG := by
  rw [Submodule.fg_def]
  exact ⟨Set.range fun j => (Pi.single j 1 : Fin 2 → K), Set.finite_range _,
    (stdLattice_eq_span R K).symm⟩

theorem stdLattice_span_top :
    Submodule.span K ((stdLattice R K : Set (Fin 2 → K))) = ⊤ := by
  rw [eq_top_iff, ← (Pi.basisFun K (Fin 2)).span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  exact Submodule.subset_span (by
    simpa only [Pi.basisFun_apply, SetLike.mem_coe] using single_one_mem_stdLattice R K j)

variable {R K}

def mulVecLinR (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    (Fin 2 → K) →ₗ[R] (Fin 2 → K) where
  toFun v := (g : Matrix (Fin 2) (Fin 2) K) *ᵥ v
  map_add' v w := Matrix.mulVec_add _ v w
  map_smul' r v := by
    rw [RingHom.id_apply]
    exact Matrix.mulVec_smul _ r v

@[simp] theorem mulVecLinR_apply (g : Matrix.GeneralLinearGroup (Fin 2) K) (v : Fin 2 → K) :
    mulVecLinR (R := R) g v = (g : Matrix (Fin 2) (Fin 2) K) *ᵥ v := rfl

def latticeMap (g : Matrix.GeneralLinearGroup (Fin 2) K) (L : Submodule R (Fin 2 → K)) :
    Submodule R (Fin 2 → K) :=
  L.map (mulVecLinR g)

theorem mem_latticeMap {g : Matrix.GeneralLinearGroup (Fin 2) K}
    {L : Submodule R (Fin 2 → K)} {v : Fin 2 → K} :
    v ∈ latticeMap g L ↔ ∃ w ∈ L, (g : Matrix (Fin 2) (Fin 2) K) *ᵥ w = v :=
  Submodule.mem_map

theorem mulVec_mem_latticeMap {g : Matrix.GeneralLinearGroup (Fin 2) K}
    {L : Submodule R (Fin 2 → K)} {w : Fin 2 → K} (hw : w ∈ L) :
    (g : Matrix (Fin 2) (Fin 2) K) *ᵥ w ∈ latticeMap g L :=
  ⟨w, hw, rfl⟩

theorem mulVecLinR_mul (g h : Matrix.GeneralLinearGroup (Fin 2) K) :
    mulVecLinR (R := R) (g * h) = (mulVecLinR g).comp (mulVecLinR h) :=
  LinearMap.ext fun v => by
    rw [LinearMap.comp_apply, mulVecLinR_apply, mulVecLinR_apply, mulVecLinR_apply,
      Matrix.mulVec_mulVec, Units.val_mul]

theorem latticeMap_one (L : Submodule R (Fin 2 → K)) : latticeMap 1 L = L := by
  have h : ∀ v : Fin 2 → K, mulVecLinR (R := R) 1 v = v := fun v => by
    rw [mulVecLinR_apply, Units.val_one, Matrix.one_mulVec]
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [show mulVecLinR (R := R) 1 w = w from h w]
    exact hw
  · intro hv
    exact ⟨v, hv, h v⟩

attribute [local simp] latticeMap_one
theorem latticeMap_mul (g h : Matrix.GeneralLinearGroup (Fin 2) K)
    (L : Submodule R (Fin 2 → K)) :
    latticeMap (g * h) L = latticeMap g (latticeMap h L) := by
  unfold latticeMap
  rw [mulVecLinR_mul, Submodule.map_comp]

theorem latticeMap_inv_latticeMap (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (L : Submodule R (Fin 2 → K)) :
    latticeMap g⁻¹ (latticeMap g L) = L := by
  rw [← latticeMap_mul, inv_mul_cancel, latticeMap_one]

theorem latticeMap_latticeMap_inv (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (L : Submodule R (Fin 2 → K)) :
    latticeMap g (latticeMap g⁻¹ L) = L := by
  rw [← latticeMap_mul, mul_inv_cancel, latticeMap_one]

theorem latticeMap_injective (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    Function.Injective (latticeMap (R := R) g) :=
  Function.LeftInverse.injective (latticeMap_inv_latticeMap g)

theorem latticeMap_mono (g : Matrix.GeneralLinearGroup (Fin 2) K)
    {L L' : Submodule R (Fin 2 → K)} (h : L ≤ L') : latticeMap g L ≤ latticeMap g L' :=
  Submodule.map_mono h

theorem le_of_latticeMap_le (g : Matrix.GeneralLinearGroup (Fin 2) K)
    {L L' : Submodule R (Fin 2 → K)} (h : latticeMap g L ≤ latticeMap g L') : L ≤ L' := by
  have := latticeMap_mono g⁻¹ h
  rwa [latticeMap_inv_latticeMap, latticeMap_inv_latticeMap] at this

theorem latticeMap_lt_latticeMap_iff (g : Matrix.GeneralLinearGroup (Fin 2) K)
    {L L' : Submodule R (Fin 2 → K)} : latticeMap g L < latticeMap g L' ↔ L < L' := by
  constructor
  · intro h
    exact lt_of_le_of_ne (le_of_latticeMap_le g h.1) (fun hEq => h.ne (by rw [hEq]))
  · intro h
    exact lt_of_le_of_ne (latticeMap_mono g h.1)
      (fun hEq => h.ne (latticeMap_injective g hEq))

def IsFullLattice (L : Submodule R (Fin 2 → K)) : Prop :=
  L.FG ∧ Submodule.span K (L : Set (Fin 2 → K)) = ⊤

theorem isFullLattice_stdLattice : IsFullLattice (stdLattice R K) :=
  ⟨stdLattice_fg R K, stdLattice_span_top R K⟩

theorem IsFullLattice.map {L : Submodule R (Fin 2 → K)} (hL : IsFullLattice L)
    (g : Matrix.GeneralLinearGroup (Fin 2) K) : IsFullLattice (latticeMap g L) := by
  refine ⟨hL.1.map _, ?_⟩
  rw [eq_top_iff]
  intro v _

  have hv : v = (g : Matrix (Fin 2) (Fin 2) K) *ᵥ
      (((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v) := by
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.one_mulVec]
  rw [hv]
  have hw : ((g⁻¹ : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v ∈
      Submodule.span K (L : Set (Fin 2 → K)) := hL.2 ▸ Submodule.mem_top
  refine Submodule.span_induction
    (p := fun w _ => (g : Matrix (Fin 2) (Fin 2) K) *ᵥ w ∈
      Submodule.span K ((latticeMap g L : Set (Fin 2 → K)))) ?_ ?_ ?_ ?_ hw
  · intro x hx
    exact Submodule.subset_span (mulVec_mem_latticeMap hx)
  · simp only [Matrix.mulVec_zero]
    exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    simp only [Matrix.mulVec_add]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    simp only [Matrix.mulVec_smul]
    exact Submodule.smul_mem _ c hx

theorem isInteger_apply_of_mem_range {g : Matrix.GeneralLinearGroup (Fin 2) K}
    (hg : g ∈ (Matrix.GeneralLinearGroup.map (n := Fin 2) (algebraMap R K)).range)
    (i j : Fin 2) : IsLocalization.IsInteger R ((g : Matrix (Fin 2) (Fin 2) K) i j) := by
  obtain ⟨h, rfl⟩ := hg
  exact ⟨h i j, (Matrix.GeneralLinearGroup.map_apply (algebraMap R K) i j h).symm⟩

theorem latticeMap_le_stdLattice_of_isInteger {g : Matrix.GeneralLinearGroup (Fin 2) K}
    (hg : ∀ i j, IsLocalization.IsInteger R ((g : Matrix (Fin 2) (Fin 2) K) i j)) :
    latticeMap g (stdLattice R K) ≤ stdLattice R K := by
  rintro _ ⟨w, hw, rfl⟩
  intro i
  show IsLocalization.IsInteger R (((g : Matrix (Fin 2) (Fin 2) K) *ᵥ w) i)
  have hcoord : ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ w) i =
      (g : Matrix (Fin 2) (Fin 2) K) i 0 * w 0 +
        (g : Matrix (Fin 2) (Fin 2) K) i 1 * w 1 := by
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  rw [hcoord]
  exact IsLocalization.isInteger_add
    (IsLocalization.isInteger_mul (hg i 0) (hw 0))
    (IsLocalization.isInteger_mul (hg i 1) (hw 1))

def scalarGL (c : Kˣ) : Matrix.GeneralLinearGroup (Fin 2) K :=
  ⟨(c : K) • 1, ((c⁻¹ : Kˣ) : K) • 1, by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Units.mul_inv,
        one_smul], by
      rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Units.inv_mul,
        one_smul]⟩

@[simp] theorem scalarGL_coe (c : Kˣ) :
    ((scalarGL c : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) =
      (c : K) • 1 := rfl

theorem scalarGL_mulVec (c : Kˣ) (v : Fin 2 → K) :
    ((scalarGL c : Matrix.GeneralLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) *ᵥ v =
      (c : K) • v := by
  rw [scalarGL_coe, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem scalarGL_mul (c c' : Kˣ) :
    (scalarGL (c * c') : Matrix.GeneralLinearGroup (Fin 2) K) = scalarGL c * scalarGL c' := by
  ext1
  rw [Units.val_mul, scalarGL_coe, scalarGL_coe, scalarGL_coe, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.one_mul, smul_smul, Units.val_mul]

theorem scalarGL_one : (scalarGL (1 : Kˣ) : Matrix.GeneralLinearGroup (Fin 2) K) = 1 := by
  ext1
  rw [scalarGL_coe, Units.val_one, one_smul, Units.val_one]

theorem scalarGL_mul_comm (c : Kˣ) (g : Matrix.GeneralLinearGroup (Fin 2) K) :
    scalarGL c * g = g * scalarGL c := by
  ext1
  rw [Units.val_mul, Units.val_mul, scalarGL_coe, Matrix.smul_mul, Matrix.mul_smul,
    Matrix.one_mul, Matrix.mul_one]

theorem mem_latticeMap_scalarGL {c : Kˣ} {L : Submodule R (Fin 2 → K)} {v : Fin 2 → K} :
    v ∈ latticeMap (scalarGL c) L ↔ ∃ w ∈ L, (c : K) • w = v := by
  rw [mem_latticeMap]
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, (scalarGL_mulVec c w).symm⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨w, hw, scalarGL_mulVec c w⟩

def Homothetic (L L' : Submodule R (Fin 2 → K)) : Prop :=
  ∃ c : Kˣ, latticeMap (scalarGL c) L = L'

theorem Homothetic.refl (L : Submodule R (Fin 2 → K)) : Homothetic L L :=
  ⟨1, by rw [scalarGL_one, latticeMap_one]⟩

theorem Homothetic.symm {L L' : Submodule R (Fin 2 → K)} (h : Homothetic L L') :
    Homothetic L' L := by
  obtain ⟨c, rfl⟩ := h
  exact ⟨c⁻¹, by
    rw [← latticeMap_mul, ← scalarGL_mul, inv_mul_cancel, scalarGL_one, latticeMap_one]⟩

theorem Homothetic.trans {L L' L'' : Submodule R (Fin 2 → K)}
    (h : Homothetic L L') (h' : Homothetic L' L'') : Homothetic L L'' := by
  obtain ⟨c, rfl⟩ := h
  obtain ⟨c', rfl⟩ := h'
  exact ⟨c' * c, by rw [scalarGL_mul, latticeMap_mul]⟩

theorem IsFullLattice.of_homothetic {L L' : Submodule R (Fin 2 → K)}
    (hL : IsFullLattice L) (h : Homothetic L L') : IsFullLattice L' := by
  obtain ⟨c, rfl⟩ := h
  exact hL.map _

variable (R K) in
def FullLattice : Type _ := {L : Submodule R (Fin 2 → K) // IsFullLattice L}

end LT.LatticeTree

namespace CerednikDrinfeld
namespace FormalOmega

structure AlgFunctor (𝒪 : Type) [CommRing 𝒪] : Type 1 where

  obj : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], Type

  map : ∀ {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B'],
    (B →ₐ[𝒪] B') → obj B → obj B'

  map_id : ∀ {B : Type} [CommRing B] [Algebra 𝒪 B] (x : obj B), map (AlgHom.id 𝒪 B) x = x

  map_comp : ∀ {B₁ : Type} [CommRing B₁] [Algebra 𝒪 B₁] {B₂ : Type} [CommRing B₂] [Algebra 𝒪 B₂]
    {B₃ : Type} [CommRing B₃] [Algebra 𝒪 B₃] (f : B₁ →ₐ[𝒪] B₂) (g : B₂ →ₐ[𝒪] B₃) (x : obj B₁),
    map (g.comp f) x = map g (map f x)

namespace AlgFunctor

variable {𝒪 : Type} [CommRing 𝒪]

structure NatTrans (F G : AlgFunctor 𝒪) : Type 1 where

  app : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], F.obj B → G.obj B

  naturality : ∀ {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B']
    (f : B →ₐ[𝒪] B') (x : F.obj B), app B' (F.map f x) = G.map f (app B x)

def NatTrans.id (F : AlgFunctor 𝒪) : NatTrans F F where
  app := fun _ _ _ x => x
  naturality _ _ := rfl

def NatTrans.comp {F G H : AlgFunctor 𝒪} (η : NatTrans F G) (θ : NatTrans G H) : NatTrans F H where
  app := fun B _ _ x => θ.app B (η.app B x)
  naturality f x := by rw [η.naturality, θ.naturality]

def NatTrans.IsIsoOnNilp (π : 𝒪) {F G : AlgFunctor 𝒪} (η : NatTrans F G) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → Function.Bijective
    (η.app B)

def NatTrans.IsMonoOnNilp (π : 𝒪) {F G : AlgFunctor 𝒪} (η : NatTrans F G) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], IsNilpotent (algebraMap 𝒪 B π) → Function.Injective
    (η.app B)

def prod (F G : AlgFunctor 𝒪) : AlgFunctor 𝒪 where
  obj B := F.obj B × G.obj B
  map f x := (F.map f x.1, G.map f x.2)
  map_id x := by rw [F.map_id, G.map_id]
  map_comp f g x := by rw [F.map_comp, G.map_comp]

def corep (A : Type) [CommRing A] [Algebra 𝒪 A] : AlgFunctor 𝒪 where
  obj B := A →ₐ[𝒪] B
  map f ψ := f.comp ψ
  map_id _ := AlgHom.ext fun _ => rfl
  map_comp _ _ _ := AlgHom.ext fun _ => rfl

structure GroupAction (Γ : Type) [Group Γ] (F : AlgFunctor 𝒪) : Type 1 where

  act : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], Γ → F.obj B → F.obj B
  act_one : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (x : F.obj B), act B 1 x = x
  act_mul : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (g h : Γ) (x : F.obj B), act B (g * h) x = act
    B g (act B h x)

  act_map : ∀ {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B']
    (f : B →ₐ[𝒪] B') (g : Γ) (x : F.obj B), F.map f (act B g x) = act B' g (F.map f x)

end AlgFunctor

section Charts

variable (𝒪 : Type) [CommRing 𝒪]

def chartV (q : ℕ) : AlgFunctor 𝒪 where
  obj B := { ζ : B // IsUnit (ζ ^ q - ζ) }
  map f x := ⟨f x.1, by
    have h := x.2.map f
    rwa [map_sub, map_pow] at h⟩
  map_id _ := Subtype.ext rfl
  map_comp _ _ _ := Subtype.ext rfl

def chartE (π : 𝒪) (q : ℕ) : AlgFunctor 𝒪 where
  obj B := { p : B × B // p.1 * p.2 = algebraMap 𝒪 B π ∧ IsUnit (p.1 ^ (q - 1) - 1) ∧ IsUnit (p.2 ^
    (q - 1) - 1) }
  map f x := ⟨(f x.1.1, f x.1.2), by
    obtain ⟨h₁, h₂, h₃⟩ := x.2
    refine ⟨?_, ?_, ?_⟩
    · rw [← map_mul, h₁, AlgHom.commutes]
    · have h := h₂.map f
      rwa [map_sub, map_pow, map_one] at h
    · have h := h₃.map f
      rwa [map_sub, map_pow, map_one] at h⟩
  map_id _ := Subtype.ext rfl
  map_comp _ _ _ := Subtype.ext rfl

def chartVUnit (q : ℕ) : AlgFunctor 𝒪 where
  obj B := { ζ : B // IsUnit (ζ ^ q - ζ) ∧ IsUnit ζ }
  map f x := ⟨f x.1, by
    obtain ⟨h₁, h₂⟩ := x.2
    refine ⟨?_, h₂.map f⟩
    have h := h₁.map f
    rwa [map_sub, map_pow] at h⟩
  map_id _ := Subtype.ext rfl
  map_comp _ _ _ := Subtype.ext rfl

def chartVUnitIncl (q : ℕ) : AlgFunctor.NatTrans (chartVUnit 𝒪 q) (chartV 𝒪 q) where
  app := fun _ _ _ x => ⟨x.1, x.2.1⟩
  naturality _ _ := Subtype.ext rfl

variable {𝒪}

theorem isUnit_pow_pred_sub_one_of_isUnit_pow_sub {B : Type} [CommRing B] {q : ℕ} (hq : 1 ≤ q) {ζ :
  B}
    (h : IsUnit (ζ ^ q - ζ)) : IsUnit (ζ ^ (q - 1) - 1) := by
  have hpow : ζ ^ q = ζ ^ (q - 1) * ζ := by
    rw [← pow_succ, Nat.sub_add_cancel hq]
  have hfac : ζ ^ q - ζ = ζ * (ζ ^ (q - 1) - 1) := by
    rw [hpow]; ring
  rw [hfac] at h
  exact isUnit_of_mul_isUnit_right h

theorem isUnit_pow_succ_sub_one_of_isNilpotent {B : Type} [CommRing B] {a : B} (ha : IsNilpotent a)
  (b : B) (n : ℕ) :
    IsUnit ((a * b) ^ (n + 1) - 1) := by
  have hab : IsNilpotent (a * b) := Commute.isNilpotent_mul_right (Commute.all a b) ha
  have hpow : IsNilpotent ((a * b) ^ (n + 1)) := by
    obtain ⟨m, hm⟩ := hab
    exact ⟨m, by rw [← pow_mul, Nat.mul_comm (n + 1) m, pow_mul, hm, zero_pow (Nat.succ_ne_zero n)]⟩
  exact hpow.isUnit_sub_one

noncomputable def vertexToEdge (π : 𝒪) {q : ℕ} (hq : 2 ≤ q) (B : Type) [CommRing B] [Algebra 𝒪 B]
    (hB : IsNilpotent (algebraMap 𝒪 B π)) (x : (chartVUnit 𝒪 q).obj B) : (chartE 𝒪 π q).obj B :=
  ⟨(x.1, algebraMap 𝒪 B π * ↑(x.2.2.unit⁻¹)), by
    refine ⟨?_, ?_, ?_⟩
    ·
      calc x.1 * (algebraMap 𝒪 B π * ↑(x.2.2.unit⁻¹))
          = algebraMap 𝒪 B π * (x.1 * ↑(x.2.2.unit⁻¹)) := by ring
        _ = algebraMap 𝒪 B π := by rw [IsUnit.mul_val_inv, mul_one]
    · exact isUnit_pow_pred_sub_one_of_isUnit_pow_sub (le_trans (by norm_num) hq) x.2.1
    · obtain ⟨n, hn⟩ : ∃ n, q - 1 = n + 1 := ⟨q - 2, by omega⟩
      rw [hn]
      exact isUnit_pow_succ_sub_one_of_isNilpotent hB _ n⟩

theorem vertexToEdge_natural (π : 𝒪) {q : ℕ} (hq : 2 ≤ q) {B : Type} [CommRing B] [Algebra 𝒪 B] {B'
  : Type} [CommRing B']
    [Algebra 𝒪 B'] (hB : IsNilpotent (algebraMap 𝒪 B π)) (hB' : IsNilpotent (algebraMap 𝒪 B' π)) (f
      : B →ₐ[𝒪] B')
    (x : (chartVUnit 𝒪 q).obj B) :
    (chartE 𝒪 π q).map f (vertexToEdge π hq B hB x) = vertexToEdge π hq B' hB' ((chartVUnit 𝒪
      q).map f x) := by
  apply Subtype.ext

  refine Prod.ext rfl ?_
  show f (algebraMap 𝒪 B π * ↑(x.2.2.unit⁻¹)) = algebraMap 𝒪 B' π * ↑(((chartVUnit 𝒪 q).map f
    x).2.2.unit⁻¹)
  rw [map_mul, AlgHom.commutes]
  congr 1
  have h1 : f x.1 * f ↑(x.2.2.unit⁻¹) = 1 := by
    rw [← map_mul, IsUnit.mul_val_inv, map_one]
  have h2 : f x.1 * ↑(((chartVUnit 𝒪 q).map f x).2.2.unit⁻¹) = 1 := by
    exact IsUnit.mul_val_inv _
  exact (IsUnit.mul_right_injective (x.2.2.map f)) (h1.trans h2.symm)

end Charts

section PadicInstance

variable (r : ℕ) [Fact r.Prime]

noncomputable abbrev padicChartV : AlgFunctor ℤ_[r] := chartV ℤ_[r] r

noncomputable abbrev padicChartE : AlgFunctor ℤ_[r] := chartE ℤ_[r] (r : ℤ_[r]) r

def SpecialFibreVertexChartShape : Prop :=
  ∀ (𝔽 : Type) [Field 𝔽] [Algebra ℤ_[r] 𝔽] [CharP 𝔽 r] (ζ : 𝔽),
    IsUnit (ζ ^ r - ζ) ↔ ∀ a : ZMod r, (ζ : 𝔽) ≠ (a.cast : 𝔽)

end PadicInstance

end FormalOmega
end CerednikDrinfeld

noncomputable section

open Polynomial

namespace CerednikDrinfeld
namespace FormalOmega

section ChartRings

variable (R : Type) [CommRing R]

abbrev vertexDiscr (q : ℕ) : R[X] := X ^ q - X

abbrev chartVRing (q : ℕ) : Type := Localization.Away (vertexDiscr R q)

namespace chartVRing

variable (q : ℕ)

def ζ : chartVRing R q := algebraMap R[X] (chartVRing R q) X

theorem algebraMap_vertexDiscr : algebraMap R[X] (chartVRing R q) (vertexDiscr R q) = ζ R q ^ q - ζ
  R q := by
  show algebraMap R[X] (chartVRing R q) (X ^ q - X) = _
  rw [map_sub, map_pow]; rfl

theorem isUnit_ζ_pow_sub : IsUnit (ζ R q ^ q - ζ R q) := by
  rw [← algebraMap_vertexDiscr]
  exact IsLocalization.Away.algebraMap_isUnit (vertexDiscr R q)

def point : (chartV R q).obj (chartVRing R q) := ⟨ζ R q, isUnit_ζ_pow_sub R q⟩

variable {R q}

theorem isUnit_aeval_of_mem_powers {B : Type} [CommRing B] [Algebra R B] (x : (chartV R q).obj B)
    (y : Submonoid.powers (vertexDiscr R q)) : IsUnit (Polynomial.aeval (R := R) x.1 (y : R[X])) :=
      by
  obtain ⟨_, n, rfl⟩ := y
  rw [map_pow]
  refine IsUnit.pow n ?_
  have : Polynomial.aeval (R := R) x.1 (vertexDiscr R q) = x.1 ^ q - x.1 := by
    show Polynomial.aeval (R := R) x.1 (X ^ q - X) = _
    rw [map_sub (Polynomial.aeval (R := R) x.1), map_pow (Polynomial.aeval (R := R) x.1),
      Polynomial.aeval_X]
  rw [this]; exact x.2

def lift {B : Type} [CommRing B] [Algebra R B] (x : (chartV R q).obj B) : chartVRing R q →ₐ[R] B :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (vertexDiscr R q)) (f := Polynomial.aeval (R :=
    R) x.1)
    (isUnit_aeval_of_mem_powers x)

@[simp] theorem lift_ζ {B : Type} [CommRing B] [Algebra R B] (x : (chartV R q).obj B) : lift x (ζ R
  q) = x.1 := by
  rw [lift, IsLocalization.liftAlgHom_apply, ζ, IsLocalization.lift_eq]
  exact Polynomial.aeval_X x.1

variable (R q) in

def corepEquiv (B : Type) [CommRing B] [Algebra R B] :
    (chartVRing R q →ₐ[R] B) ≃ (chartV R q).obj B where
  toFun φ := (chartV R q).map φ (point R q)
  invFun x := lift x
  left_inv φ := by
    apply IsLocalization.algHom_ext (Submonoid.powers (vertexDiscr R q))
    apply Polynomial.algHom_ext
    show lift ((chartV R q).map φ (point R q)) (algebraMap R[X] _ X) = φ (algebraMap R[X] _ X)
    exact lift_ζ _
  right_inv x := Subtype.ext (lift_ζ x)

@[simp] theorem corepEquiv_apply_val (B : Type) [CommRing B] [Algebra R B] (φ : chartVRing R q
  →ₐ[R] B) :
    (corepEquiv R q B φ).1 = φ (ζ R q) := rfl

theorem corepEquiv_natural {B : Type} [CommRing B] [Algebra R B] {B' : Type} [CommRing B'] [Algebra
  R B']
    (f : B →ₐ[R] B') (φ : chartVRing R q →ₐ[R] B) :
    corepEquiv R q B' ((AlgFunctor.corep (𝒪 := R) (chartVRing R q)).map f φ) = (chartV R q).map f
      (corepEquiv R q B φ) :=
  Subtype.ext rfl

variable (R q) in

def corepNatTrans : AlgFunctor.NatTrans (AlgFunctor.corep (𝒪 := R) (chartVRing R q)) (chartV R q)
  where
  app B _ _ φ := corepEquiv R q B φ
  naturality f φ := corepEquiv_natural f φ

end chartVRing

abbrev edgeRel (π : R) : MvPolynomial (Fin 2) R := MvPolynomial.X 0 * MvPolynomial.X 1 -
  MvPolynomial.C π

def edgeQuot (π : R) : Type := MvPolynomial (Fin 2) R ⧸ Ideal.span {edgeRel R π}

instance edgeQuot.instCommRing (π : R) : CommRing (edgeQuot R π) :=
  show CommRing (MvPolynomial (Fin 2) R ⧸ Ideal.span {edgeRel R π}) from inferInstance

instance edgeQuot.instAlgebra (π : R) : Algebra R (edgeQuot R π) :=
  show Algebra R (MvPolynomial (Fin 2) R ⧸ Ideal.span {edgeRel R π}) from inferInstance

def edgeQuot.mk (π : R) : MvPolynomial (Fin 2) R →ₐ[R] edgeQuot R π :=
  Ideal.Quotient.mkₐ R (Ideal.span {edgeRel R π})

theorem edgeQuot.mk_edgeRel (π : R) : edgeQuot.mk R π (edgeRel R π) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

abbrev edgeDiscr (q : ℕ) : MvPolynomial (Fin 2) R :=
  (MvPolynomial.X 0 ^ (q - 1) - 1) * (MvPolynomial.X 1 ^ (q - 1) - 1)

def edgeQuot.discr (π : R) (q : ℕ) : edgeQuot R π := edgeQuot.mk R π (edgeDiscr R q)

abbrev chartERing (π : R) (q : ℕ) : Type := Localization.Away (edgeQuot.discr R π q)

namespace chartERing

variable (π : R) (q : ℕ)

def ofPoly : MvPolynomial (Fin 2) R →ₐ[R] chartERing R π q :=
  (Algebra.algHom R (edgeQuot R π) (chartERing R π q)).comp (edgeQuot.mk R π)

def ξ : chartERing R π q := ofPoly R π q (MvPolynomial.X 0)

def η : chartERing R π q := ofPoly R π q (MvPolynomial.X 1)

theorem ofPoly_edgeRel : ofPoly R π q (edgeRel R π) = 0 := by
  rw [ofPoly, AlgHom.comp_apply, edgeQuot.mk_edgeRel, map_zero]

theorem ξ_mul_η : ξ R π q * η R π q = algebraMap R (chartERing R π q) π := by
  have hC : ofPoly R π q (MvPolynomial.C π) = algebraMap R (chartERing R π q) π := (ofPoly R π
    q).commutes π
  have h2 : ofPoly R π q (edgeRel R π) = ξ R π q * η R π q - algebraMap R (chartERing R π q) π := by
    show ofPoly R π q (MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C π) = _
    rw [map_sub (ofPoly R π q), map_mul (ofPoly R π q), hC]; rfl
  rw [← sub_eq_zero, ← h2, ofPoly_edgeRel]

theorem ofPoly_edgeDiscr :
    ofPoly R π q (edgeDiscr R q) = (ξ R π q ^ (q - 1) - 1) * (η R π q ^ (q - 1) - 1) := by
  show ofPoly R π q ((MvPolynomial.X 0 ^ (q - 1) - 1) * (MvPolynomial.X 1 ^ (q - 1) - 1)) = _
  rw [map_mul (ofPoly R π q), map_sub (ofPoly R π q), map_sub (ofPoly R π q), map_pow (ofPoly R π
    q),
    map_pow (ofPoly R π q), map_one]; rfl

theorem isUnit_discr : IsUnit ((ξ R π q ^ (q - 1) - 1) * (η R π q ^ (q - 1) - 1)) := by
  rw [← ofPoly_edgeDiscr]
  exact IsLocalization.Away.algebraMap_isUnit (edgeQuot.discr R π q)

def point : (chartE R π q).obj (chartERing R π q) :=
  ⟨(ξ R π q, η R π q), ξ_mul_η R π q, isUnit_of_mul_isUnit_left (isUnit_discr R π q),
    isUnit_of_mul_isUnit_right (isUnit_discr R π q)⟩

variable {R π q}

abbrev evalPoly {B : Type} [CommRing B] [Algebra R B] (x : (chartE R π q).obj B) : MvPolynomial
  (Fin 2) R →ₐ[R] B :=
  MvPolynomial.aeval (fun i : Fin 2 => if i = 0 then x.1.1 else x.1.2)

@[simp] theorem evalPoly_X_zero {B : Type} [CommRing B] [Algebra R B] (x : (chartE R π q).obj B) :
    evalPoly x (MvPolynomial.X 0) = x.1.1 := by simp [evalPoly, MvPolynomial.aeval_X]

@[simp] theorem evalPoly_X_one {B : Type} [CommRing B] [Algebra R B] (x : (chartE R π q).obj B) :
    evalPoly x (MvPolynomial.X 1) = x.1.2 := by simp [evalPoly, MvPolynomial.aeval_X]

theorem evalPoly_edgeRel {B : Type} [CommRing B] [Algebra R B] (x : (chartE R π q).obj B) :
    evalPoly x (edgeRel R π) = 0 := by
  have hC : evalPoly x (MvPolynomial.C π) = algebraMap R B π := (evalPoly x).commutes π
  show evalPoly x (MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C π) = 0
  rw [map_sub (evalPoly x), map_mul (evalPoly x), evalPoly_X_zero, evalPoly_X_one, hC, x.2.1,
    sub_self]

def evalQuot {B : Type} [CommRing B] [Algebra R B] (x : (chartE R π q).obj B) : edgeQuot R π →ₐ[R]
  B :=
  Ideal.Quotient.liftₐ (Ideal.span {edgeRel R π}) (evalPoly x) (fun a ha => by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [map_mul (evalPoly x), evalPoly_edgeRel, mul_zero])

theorem evalQuot_mk {B : Type} [CommRing B] [Algebra R B] (x : (chartE R π q).obj B) (p :
  MvPolynomial (Fin 2) R) :
    evalQuot x (edgeQuot.mk R π p) = evalPoly x p := rfl

theorem isUnit_evalQuot_of_mem_powers {B : Type} [CommRing B] [Algebra R B] (x : (chartE R π q).obj
  B)
    (y : Submonoid.powers (edgeQuot.discr R π q)) :
    IsUnit (evalQuot x (y : edgeQuot R π)) := by
  obtain ⟨_, n, rfl⟩ := y
  rw [map_pow]
  refine IsUnit.pow n ?_
  rw [edgeQuot.discr, evalQuot_mk]
  show IsUnit (evalPoly x ((MvPolynomial.X 0 ^ (q - 1) - 1) * (MvPolynomial.X 1 ^ (q - 1) - 1)))
  rw [map_mul (evalPoly x), map_sub (evalPoly x), map_sub (evalPoly x), map_pow (evalPoly x),
    map_pow (evalPoly x),
    map_one, evalPoly_X_zero, evalPoly_X_one]
  exact x.2.2.1.mul x.2.2.2

def lift {B : Type} [CommRing B] [Algebra R B] (x : (chartE R π q).obj B) : chartERing R π q →ₐ[R]
  B :=
  IsLocalization.liftAlgHom (M := Submonoid.powers (edgeQuot.discr R π q))
    (f := evalQuot x) (isUnit_evalQuot_of_mem_powers x)

theorem lift_ofPoly {B : Type} [CommRing B] [Algebra R B] (x : (chartE R π q).obj B) (p :
  MvPolynomial (Fin 2) R) :
    lift x (ofPoly R π q p) = evalPoly x p := by
  rw [lift, IsLocalization.liftAlgHom_apply, ofPoly, AlgHom.comp_apply]
  exact (IsLocalization.lift_eq _ _).trans (evalQuot_mk x p)

@[simp] theorem lift_ξ {B : Type} [CommRing B] [Algebra R B] (x : (chartE R π q).obj B) : lift x (ξ
  R π q) = x.1.1 := by
  rw [ξ, lift_ofPoly, evalPoly_X_zero]

@[simp] theorem lift_η {B : Type} [CommRing B] [Algebra R B] (x : (chartE R π q).obj B) : lift x (η
  R π q) = x.1.2 := by
  rw [η, lift_ofPoly, evalPoly_X_one]

variable (R π q) in

def corepEquiv (B : Type) [CommRing B] [Algebra R B] :
    (chartERing R π q →ₐ[R] B) ≃ (chartE R π q).obj B where
  toFun φ := (chartE R π q).map φ (point R π q)
  invFun x := lift x
  left_inv φ := by
    apply IsLocalization.algHom_ext (Submonoid.powers (edgeQuot.discr R π q))
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    show lift ((chartE R π q).map φ (point R π q)) (ofPoly R π q (MvPolynomial.X i)) = φ (ofPoly R
      π q (MvPolynomial.X i))
    fin_cases i
    · exact lift_ξ _
    · exact lift_η _
  right_inv x := Subtype.ext (Prod.ext (lift_ξ x) (lift_η x))

@[simp] theorem corepEquiv_apply_val (B : Type) [CommRing B] [Algebra R B] (φ : chartERing R π q
  →ₐ[R] B) :
    (corepEquiv R π q B φ).1 = (φ (ξ R π q), φ (η R π q)) := rfl

theorem corepEquiv_natural {B : Type} [CommRing B] [Algebra R B] {B' : Type} [CommRing B'] [Algebra
  R B']
    (f : B →ₐ[R] B') (φ : chartERing R π q →ₐ[R] B) :
    corepEquiv R π q B' ((AlgFunctor.corep (𝒪 := R) (chartERing R π q)).map f φ) = (chartE R π
      q).map f (corepEquiv R π q B φ) :=
  Subtype.ext rfl

variable (R π q) in

def corepNatTrans : AlgFunctor.NatTrans (AlgFunctor.corep (𝒪 := R) (chartERing R π q)) (chartE R π
  q) where
  app B _ _ φ := corepEquiv R π q B φ
  naturality f φ := corepEquiv_natural f φ

end chartERing

section Level

variable (𝒪 : Type) [CommRing 𝒪] (π : 𝒪) (q n : ℕ)

abbrev truncRing : Type := 𝒪 ⧸ Ideal.span {π ^ (n + 1)}

abbrev chartVRingMod : Type := chartVRing (truncRing 𝒪 π n) q

abbrev chartERingMod : Type :=
  chartERing (truncRing 𝒪 π n) (Ideal.Quotient.mk (Ideal.span {π ^ (n + 1)}) π) q

theorem isNilpotent_algebraMap_of_isScalarTower (B : Type) [CommRing B] [Algebra 𝒪 B]
    [Algebra (truncRing 𝒪 π n) B] [IsScalarTower 𝒪 (truncRing 𝒪 π n) B] : IsNilpotent (algebraMap 𝒪
      B π) := by
  refine ⟨n + 1, ?_⟩
  rw [← map_pow, IsScalarTower.algebraMap_apply 𝒪 (truncRing 𝒪 π n) B,
    Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span
      (Set.mem_singleton _)),
    map_zero]

end Level

end ChartRings

end FormalOmega
end CerednikDrinfeld

end

open scoped TensorProduct
open LT.LatticeTree

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
  ⟨latticeMap g M.1, M.2.map g⟩

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

section OmegaNr

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] (π : 𝒪)
variable (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
variable (vdet : Matrix.GeneralLinearGroup (Fin 2) K →* Multiplicative ℤ)

abbrev OmegaNrObj (B : Type) [CommRing B] [Algebra 𝒪 B] : Type :=
  (Onr →ₐ[𝒪] B) × OmegaObj (K := K) π B

noncomputable def frobTwist (n : ℤ) {B : Type} [CommRing B] [Algebra 𝒪 B] (ψ : Onr →ₐ[𝒪] B) : Onr
  →ₐ[𝒪] B :=
  ψ.comp ((Fr ^ n : Onr ≃ₐ[𝒪] Onr) : Onr →ₐ[𝒪] Onr)

def OmegaNr.IsTwistedAct (B : Type) [CommRing B] [Algebra 𝒪 B] (g : Matrix.GeneralLinearGroup (Fin
  2) K)
    (x x' : OmegaNrObj (K := K) π Onr B) : Prop :=
  x'.1 = frobTwist Onr Fr (- Multiplicative.toAdd (vdet g)) x.1 ∧
    DeligneDatum.IsPullback (K := K) (π := π) B g⁻¹ x.2 x'.2

end OmegaNr

end FormalOmega
end CerednikDrinfeld
