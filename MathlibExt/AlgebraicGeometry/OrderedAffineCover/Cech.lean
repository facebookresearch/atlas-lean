/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicGeometry_OrderedAffineCoverCech.lean`,
`Definitions/Def_AlgebraicGeometry_TwoAffineOpenCover.lean`
and
`Definitions/Def_AlgebraicGeometry_OrderedAffineCoverComap.lean`
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

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.Module.LinearMap.Basic

/-!
# Čech cochains of an ordered finite affine cover

An `OrderedAffineCover` of a scheme `V` is a finite, linearly ordered family of affine
opens covering `V`. For a presheaf of modules `F` on `V` over a base `Spec R`, the
alternating Čech cochains of degree `i` are families of sections of `F` indexed by
strictly increasing `(i + 1)`-tuples of indices, and `OModulePresheaf.d` is the usual
alternating Čech differential.

## Main definitions

* `AlgebraicGeometry.Scheme.OrderedAffineCover`: a finite ordered affine open cover.
* `AlgebraicGeometry.OModulePresheaf`: a presheaf of `R`-modules on `V` whose sections over
  `U` are also `Γ(V, U)`-modules, compatibly with restriction.
* `AlgebraicGeometry.OModulePresheaf.d`: the alternating Čech differential.
* `AlgebraicGeometry.OModulePresheaf.unit`: the structure presheaf `U ↦ Γ(V, U)`.

Mathlib's `CategoryTheory.cechComplexFunctor` is the Čech complex indexed by all tuples
`Fin (n + 1) → ι`; the cochains here are the alternating ones, indexed by strictly increasing
tuples, as in the source.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace

namespace Scheme.Hom

variable {R : Type u} [CommRing R] {X : Scheme.{u}}

/-- The `R`-algebra structure on `Γ(X, U)` induced by a morphism `X ⟶ Spec R`. -/
@[reducible] def sectionsAlgebra (c : X ⟶ Spec (.of R)) (U : X.Opens) : Algebra R Γ(X, U) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ c.appLE ⊤ U le_top).hom.toAlgebra

/-- Restriction of sections `Γ(X, U) → Γ(X, V)` as a morphism of `R`-algebras, for the
algebra structures induced by `c : X ⟶ Spec R`. -/
def sectionsRestrictAlgHom (c : X ⟶ Spec (.of R)) {U V : X.Opens} (h : V ≤ U) :
    letI := c.sectionsAlgebra U; letI := c.sectionsAlgebra V
    Γ(X, U) →ₐ[R] Γ(X, V) :=
  letI := c.sectionsAlgebra U; letI := c.sectionsAlgebra V
  { (X.presheaf.map (homOfLE h).op).hom with
    commutes' := fun r => congrArg (fun f => f.hom ((Scheme.ΓSpecIso (.of R)).inv.hom r))
      (Scheme.Hom.appLE_map c le_top (homOfLE h).op) }

end Scheme.Hom

/-- A finite, linearly ordered family of affine opens covering `V`. -/
structure Scheme.OrderedAffineCover (V : Scheme.{u}) where
  /-- The index type. -/
  ι : Type u
  [instFintype : Fintype ι]
  [instLinearOrder : LinearOrder ι]
  /-- The opens of the cover. -/
  U : ι → V.Opens
  isAffineOpen : ∀ i, IsAffineOpen (U i)
  iSup_eq_top : ⨆ i, U i = ⊤

attribute [instance] Scheme.OrderedAffineCover.instFintype
  Scheme.OrderedAffineCover.instLinearOrder

namespace Scheme.OrderedAffineCover

variable {V : Scheme.{u}} (K : V.OrderedAffineCover)

/-- Strictly increasing `(i + 1)`-tuples of indices: the index set of alternating Čech
cochains of degree `i`. -/
def Idx (i : ℕ) : Type u := {s : Fin (i + 1) → K.ι // StrictMono s}

instance instFintypeIdx (i : ℕ) : Fintype (K.Idx i) := Subtype.fintype _

instance instDecidableEqIdx (i : ℕ) : DecidableEq (K.Idx i) := Classical.decEq _

/-- The intersection of the opens indexed by a tuple. -/
def inter {i : ℕ} (s : K.Idx i) : V.Opens := ⨅ j, K.U (s.1 j)

/-- The `j`-th face of a strictly increasing tuple: delete its `j`-th entry. -/
def face {i : ℕ} (s : K.Idx (i + 1)) (j : Fin (i + 2)) : K.Idx i :=
  ⟨s.1 ∘ Fin.succAbove j, s.2.comp (Fin.strictMono_succAbove j)⟩

theorem face_val {i : ℕ} (s : K.Idx (i + 1)) (j : Fin (i + 2)) :
    (K.face s j).1 = s.1 ∘ Fin.succAbove j :=
  rfl

theorem inter_le {i : ℕ} (s : K.Idx i) (j : Fin (i + 1)) : K.inter s ≤ K.U (s.1 j) :=
  iInf_le _ j

theorem inter_le_inter_face {i : ℕ} (s : K.Idx (i + 1)) (j : Fin (i + 2)) :
    K.inter s ≤ K.inter (K.face s j) :=
  le_iInf fun k => iInf_le _ (j.succAbove k)

/-- Preimages commute with finite infima of opens indexed by `Fin (n + 1)`. -/
theorem preimage_iInf_fin {Y Z : Scheme.{u}} (f : Y ⟶ Z) {n : ℕ} (W : Fin (n + 1) → Z.Opens) :
    f ⁻¹ᵁ (⨅ j, W j) = ⨅ j, f ⁻¹ᵁ (W j) := by
  have hsplit : ∀ {α : Type u} [CompleteLattice α] {m : ℕ} (g : Fin (m + 2) → α),
      (⨅ j : Fin (m + 2), g j) = g 0 ⊓ (⨅ j : Fin (m + 1), g j.succ) := fun g =>
    le_antisymm (le_inf (iInf_le _ 0) (le_iInf fun j => iInf_le _ j.succ))
      (le_iInf fun j => Fin.cases inf_le_left (fun k => inf_le_right.trans (iInf_le _ k)) j)
  induction n with
  | zero =>
    simp only [show (⨅ j : Fin 1, W j) = W 0 from
      le_antisymm (iInf_le _ 0) (le_iInf fun j => by fin_cases j; exact le_rfl),
      show (⨅ j : Fin 1, f ⁻¹ᵁ (W j)) = f ⁻¹ᵁ (W 0) from
      le_antisymm (iInf_le _ 0) (le_iInf fun j => by fin_cases j; exact le_rfl)]
  | succ m ih =>
    rw [hsplit W, Scheme.Hom.preimage_inf, ih (fun j => W j.succ),
      hsplit (fun j => f ⁻¹ᵁ (W j))]

end Scheme.OrderedAffineCover

/-- A presheaf of `R`-modules on a scheme `V` over `Spec R`, whose sections over `U` are
also `Γ(V, U)`-modules compatibly with the `R`-structure and with restriction. -/
structure OModulePresheaf {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) where
  /-- The sections over an open. -/
  obj : V.Opens → Type u
  [addCommGroup : ∀ U, AddCommGroup (obj U)]
  [module : ∀ U, Module R (obj U)]
  [moduleSections : ∀ U, Module Γ(V, U) (obj U)]
  [isScalarTower : ∀ U, letI := π.sectionsAlgebra U
    IsScalarTower R Γ(V, U) (obj U)]
  /-- Restriction of sections. -/
  res : ∀ {U U' : V.Opens}, U ≤ U' → obj U' →ₗ[R] obj U
  res_smul : ∀ {U U' : V.Opens} (h : U ≤ U') (a : Γ(V, U')) (x : obj U'),
    res h (a • x) = (V.presheaf.map (homOfLE h).op).hom a • res h x
  res_refl : ∀ U, res (le_refl U) = LinearMap.id
  res_comp : ∀ {U U' U'' : V.Opens} (h : U ≤ U') (h' : U' ≤ U''),
    res (h.trans h') = res h ∘ₗ res h'

attribute [instance] OModulePresheaf.addCommGroup OModulePresheaf.module
  OModulePresheaf.moduleSections OModulePresheaf.isScalarTower

namespace OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable (F : OModulePresheaf π) (K : V.OrderedAffineCover)

theorem res_refl_apply (U : V.Opens) (x : F.obj U) : F.res (le_refl U) x = x := by
  rw [F.res_refl]; rfl

theorem res_res {U U' U'' : V.Opens} (h : U ≤ U') (h' : U' ≤ U'') (x : F.obj U'') :
    F.res h (F.res h' x) = F.res (h.trans h') x := by
  rw [F.res_comp h h']; rfl

/-- Alternating Čech cochains of degree `i` of `F` on the cover `K`. -/
abbrev cochain (i : ℕ) : Type u := ∀ s : K.Idx i, F.obj (K.inter s)

/-- The alternating Čech differential. -/
def d (i : ℕ) : F.cochain K i →ₗ[R] F.cochain K (i + 1) :=
  LinearMap.pi fun s => ∑ j : Fin (i + 2), ((-1 : ℤ) ^ (j : ℕ)) •
    ((F.res (K.inter_le_inter_face s j)).comp (LinearMap.proj (K.face s j)))

theorem d_apply (i : ℕ) (c : F.cochain K i) (s : K.Idx (i + 1)) :
    F.d K i c s = ∑ j : Fin (i + 2), ((-1 : ℤ) ^ (j : ℕ)) •
      F.res (K.inter_le_inter_face s j) (c (K.face s j)) := by
  simp only [d, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.smul_apply,
    LinearMap.comp_apply, LinearMap.proj_apply]

variable (π) in
/-- The structure presheaf `U ↦ Γ(V, U)` as an `OModulePresheaf`. -/
def unit : OModulePresheaf π where
  obj U := Γ(V, U)
  addCommGroup _ := inferInstance
  module U := (π.sectionsAlgebra U).toModule
  moduleSections _ := Semiring.toModule
  isScalarTower U := by
    let := π.sectionsAlgebra U
    exact IsScalarTower.right
  res {U U'} h :=
    letI := π.sectionsAlgebra U
    letI := π.sectionsAlgebra U'
    (π.sectionsRestrictAlgHom h).toLinearMap
  res_smul h a x := by
    change (V.presheaf.map (homOfLE h).op).hom (a * x)
      = (V.presheaf.map (homOfLE h).op).hom a * (V.presheaf.map (homOfLE h).op).hom x
    exact map_mul _ a x
  res_refl U := by
    let := π.sectionsAlgebra U
    refine LinearMap.ext fun x => ?_
    change (V.presheaf.map (homOfLE (le_refl U)).op).hom x = x
    rw [Subsingleton.elim (homOfLE (le_refl U)).op (𝟙 (op U)), V.presheaf.map_id]; rfl
  res_comp {U U' U''} h h' := by
    let := π.sectionsAlgebra U
    let := π.sectionsAlgebra U''
    refine LinearMap.ext fun x => ?_
    change (V.presheaf.map (homOfLE (h.trans h')).op).hom x
      = (V.presheaf.map (homOfLE h).op).hom ((V.presheaf.map (homOfLE h').op).hom x)
    rw [← CommRingCat.comp_apply, ← V.presheaf.map_comp]; rfl

theorem unit_obj (U : V.Opens) : (unit π).obj U = Γ(V, U) := rfl

theorem unit_res_apply {U U' : V.Opens} (h : U ≤ U') (x : (unit π).obj U') :
    (unit π).res h x = (V.presheaf.map (homOfLE h).op).hom (x : Γ(V, U')) :=
  rfl

theorem unit_smul (U : V.Opens) (a : Γ(V, U)) (x : (unit π).obj U) :
    a • x = HMul.hMul (α := Γ(V, U)) (β := Γ(V, U)) a x := rfl

end OModulePresheaf

end AlgebraicGeometry
