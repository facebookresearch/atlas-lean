/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicGeometry_DescentCharacter.lean`,
`Definitions/Def_AlgebraicGeometry_RelativePicardFunctor.lean`,
`Theorems/Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_app_eq_smul.lean`,
`P2M/Sol/S_AlgebraicGeometry_Scheme_Modules_IsInvertible_existsUnique_app_eq_smul.lean`,
the DescentCharacter existsUnique theorem file in `Theorems/`
and its proof file in `P2M/Sol/`
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

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

/-!
# Endomorphisms of invertible sheaves are base scalars

An invertible sheaf is a module sheaf that is locally isomorphic to the
structure sheaf (`CoherentCurveLinearSeries.IsLineBundle`). Every endomorphism
of an invertible sheaf is, on each open, multiplication by the restriction of a
unique global section. When the global sections of `X` are exactly the base
ring (the map from the base ring to them is bijective), that section comes from
a unique base scalar.
-/

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries (IsLineBundle structureModule)

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

lemma Hom.app_naturality {M N : X.Modules} (φ : M ⟶ N) {U V : X.Opens} (i : U ⟶ V) (x : Γ(M, V)) :
    φ.app U (M.presheaf.map i.op x) = N.presheaf.map i.op (φ.app V x) := by
  have h := φ.mapPresheaf.naturality i.op
  simp only [mapPresheaf_app] at h
  have h' := ConcreteCategory.congr_hom h x
  simp only [ConcreteCategory.comp_apply] at h'
  exact h'

noncomputable def unitOne (U : X.Opens) : Γ(structureModule X, U) := (1 : Γ(X, U))

def toΓ {U : X.Opens} (x : Γ(structureModule X, U)) : Γ(X, U) := x

lemma eq_toΓ_smul_unitOne {U : X.Opens} (x : Γ(structureModule X, U)) :
    x = toΓ x • unitOne U :=
  (mul_one (toΓ x)).symm

lemma map_unitOne {U V : X.Opens} (i : U ⟶ V) :
    (structureModule X).presheaf.map i.op (unitOne V) = unitOne U :=
  map_one (X.presheaf.map i.op).hom

variable (M : X.Modules) (g : M ⟶ M)

def Represents (V : X.Opens) (s : Γ(X, V)) : Prop :=
  ∀ (W : X.Opens) (h : W ≤ V) (x : Γ(M, W)), g.app W x = X.presheaf.map (homOfLE h).op s • x

variable {M g}

lemma Represents.restrict {V V' : X.Opens} (h : V' ≤ V) {s : Γ(X, V)} (hs : Represents M g V s) :
    Represents M g V' (X.presheaf.map (homOfLE h).op s) := by
  intro W hW x
  rw [hs W (hW.trans h) x, ← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

lemma presheaf_map_map {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (s : Γ(X, U)) :
    X.presheaf.map (homOfLE h₂).op (X.presheaf.map (homOfLE h₁).op s) =
      X.presheaf.map (homOfLE (h₂.trans h₁)).op s := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

lemma module_map_map {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(M, U)) :
    M.presheaf.map (homOfLE h₂).op (M.presheaf.map (homOfLE h₁).op x) =
      M.presheaf.map (homOfLE (h₂.trans h₁)).op x := by
  rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
  rfl

lemma Represents.of_cover {V : X.Opens} {ι : Type*} (Vi : ι → X.Opens) (hVi : ∀ i, Vi i ≤ V)
    (hcov : V ≤ iSup Vi) (s : Γ(X, V))
    (h : ∀ i, Represents M g (Vi i) (X.presheaf.map (homOfLE (hVi i)).op s)) :
    Represents M g V s := by
  intro W hW x
  have hWcov : W ≤ ⨆ i, W ⊓ Vi i := by
    rw [← inf_iSup_eq]
    exact le_inf le_rfl (hW.trans hcov)
  apply TopCat.Sheaf.eq_of_locally_eq' (⟨M.presheaf, M.isSheaf⟩ : TopCat.Sheaf Ab X)
    (fun i => W ⊓ Vi i) W
    (fun i => homOfLE inf_le_left) hWcov
  intro i
  change M.presheaf.map (homOfLE (inf_le_left : W ⊓ Vi i ≤ W)).op (g.app W x) =
    M.presheaf.map (homOfLE (inf_le_left : W ⊓ Vi i ≤ W)).op (X.presheaf.map (homOfLE hW).op s • x)
  rw [← Hom.app_naturality, Modules.map_smul, presheaf_map_map,
    h i (W ⊓ Vi i) inf_le_right, presheaf_map_map]

def TrivOn (M : X.Modules) (V : X.Opens) : Prop :=
  ∃ e : Γ(M, V), ∀ (W : X.Opens) (h : W ≤ V),
    Function.Bijective (fun r : Γ(X, W) => r • M.presheaf.map (homOfLE h).op e)

lemma TrivOn.restrict {V V' : X.Opens} (h : V' ≤ V) (hV : TrivOn M V) : TrivOn M V' := by
  obtain ⟨e, he⟩ := hV
  refine ⟨M.presheaf.map (homOfLE h).op e, fun W hW => ?_⟩
  simp only [module_map_map]
  exact he W (hW.trans h)

lemma exists_represents_of_trivOn {V : X.Opens} (hV : TrivOn M V) : ∃ s, Represents M g V s := by
  obtain ⟨e, he⟩ := hV
  obtain ⟨s, hs⟩ := (he V le_rfl).2 (g.app V (M.presheaf.map (homOfLE le_rfl).op e))
  refine ⟨s, fun W hW x => ?_⟩
  obtain ⟨r, rfl⟩ := (he W hW).2 x
  dsimp only
  rw [Hom.app_smul]
  have h1 : g.app W (M.presheaf.map (homOfLE hW).op e) =
      X.presheaf.map (homOfLE hW).op s • M.presheaf.map (homOfLE hW).op e := by
    have h2 := congrArg (M.presheaf.map (homOfLE hW).op) hs
    dsimp only at h2
    rw [Modules.map_smul, module_map_map, ← Hom.app_naturality, module_map_map] at h2
    exact h2.symm
  rw [h1, smul_smul, smul_smul, mul_comm]

lemma represents_unique_of_trivOn {V : X.Opens} (hV : TrivOn M V) {s s' : Γ(X, V)}
    (hs : Represents M g V s) (hs' : Represents M g V s') : s = s' := by
  obtain ⟨e, he⟩ := hV
  have h := (hs V le_rfl (M.presheaf.map (homOfLE le_rfl).op e)).symm.trans
    (hs' V le_rfl (M.presheaf.map (homOfLE le_rfl).op e))
  have h' := (he V le_rfl).1 h
  simpa using h'

lemma trivOn_of_iso (U : X.Opens) (τ : (Modules.pullback U.ι).obj M ≅ structureModule U) :
    TrivOn M (U.ι ''ᵁ ⊤) := by
  let τ' : M.restrict U.ι ≅ structureModule (U : Scheme.{u}) :=
    (restrictFunctorIsoPullback U.ι).app M ≪≫ τ
  let e : Γ(M, U.ι ''ᵁ ⊤) := τ'.inv.app ⊤ (unitOne ⊤)
  refine ⟨e, fun W hW => ?_⟩
  obtain ⟨W', rfl⟩ : ∃ W' : (U : Scheme.{u}).Opens, W = U.ι ''ᵁ W' :=
    ⟨U.ι ⁻¹ᵁ W, by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
        inf_eq_right.mpr (hW.trans_eq (Scheme.Opens.ι_image_top U))]⟩
  have key : ∀ r : Γ(X, U.ι ''ᵁ W'),
      r • M.presheaf.map (homOfLE hW).op e =
        τ'.inv.app W' (@id Γ(structureModule (U : Scheme.{u}), W') r) := by
    intro r
    have hr : (@id Γ(structureModule (U : Scheme.{u}), W') r) =
        toΓ (@id Γ(structureModule (U : Scheme.{u}), W') r) • unitOne W' :=
      eq_toΓ_smul_unitOne _
    rw [hr, Hom.app_smul]
    have hn := Hom.app_naturality τ'.inv (homOfLE (le_top : W' ≤ ⊤)) (unitOne ⊤)
    rw [map_unitOne] at hn
    rw [hn]
    change _ = ((U.ι.appIso W').inv.hom
        (toΓ (@id Γ(structureModule (U : Scheme.{u}), W') r))) •
      M.presheaf.map (homOfLE hW).op e
    rw [Scheme.Opens.ι_appIso]
    rfl
  have hbij : Function.Bijective (τ'.inv.app W') :=
    ConcreteCategory.bijective_of_isIso (τ'.inv.app W')
  rw [show (fun r : Γ(X, U.ι ''ᵁ W') => r • M.presheaf.map (homOfLE hW).op e) =
      fun r => τ'.inv.app W' (@id Γ(structureModule (U : Scheme.{u}), W') r) from funext key]
  exact hbij

end AlgebraicGeometry.Scheme.Modules

namespace MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- Every endomorphism of an invertible sheaf is multiplication by a
unique global section of the structure sheaf. -/
public theorem IsLineBundle.existsUnique_app_eq_smul {M : X.Modules}
    (hM : IsLineBundle M) (g : M ⟶ M) :
    ∃! s : Γ(X, ⊤), ∀ (U : X.Opens) (x : Γ(M, U)),
      g.app U x = X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op s • x := by
  choose U hxU hτ using hM
  have htriv : ∀ x, TrivOn M (U x) := fun x => by
    have h := trivOn_of_iso (M := M) (U x) (hτ x).some
    rwa [Scheme.Opens.ι_image_top] at h
  have hcov : (⊤ : X.Opens) ≤ iSup U := fun y _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hxU y⟩
  choose s hs using fun x => exists_represents_of_trivOn (g := g) (htriv x)
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf U s := fun i j =>
    represents_unique_of_trivOn ((htriv i).restrict inf_le_left)
      ((hs i).restrict inf_le_left) ((hs j).restrict inf_le_right)
  obtain ⟨S, hS, -⟩ := X.sheaf.existsUnique_gluing' U ⊤ (fun i => homOfLE le_top) hcov s hcompat
  have hS' : ∀ i, X.presheaf.map (homOfLE (le_top : U i ≤ ⊤)).op (S : Γ(X, ⊤)) = s i := hS
  have hrep : Represents M g ⊤ S :=
    Represents.of_cover U (fun _ => le_top) hcov S (fun i => by rw [hS' i]; exact hs i)
  refine ⟨S, fun W x => hrep W le_top x, fun S' hS' => ?_⟩
  have hrep' : Represents M g ⊤ S' := fun W hW x => hS' W x
  apply X.sheaf.eq_of_locally_eq' U ⊤ (fun i => homOfLE le_top) hcov
  intro i
  exact represents_unique_of_trivOn (htriv i) (hrep'.restrict le_top) (hrep.restrict le_top)

end MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

namespace AlgebraicGeometry.DescentCharacter

variable {X : Scheme.{u}} {R : Type u} [CommRing R]

/-- The section of the structure sheaf over `U` coming from `c : R`. -/
@[expose] public noncomputable def baseSection (f : X ⟶ Spec (CommRingCat.of R)) (c : R)
    (U : X.Opens) : Γ(X, U) :=
  X.presheaf.map (homOfLE (le_top (a := U))).op
    (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv c))

/-- `σ` is multiplication by the base scalar `c` on every open. -/
@[expose] public noncomputable def IsBaseScalar (f : X ⟶ Spec (CommRingCat.of R))
    {M : X.Modules} (σ : M ⟶ M) (c : R) : Prop :=
  ∀ (U : X.Opens) (s : Γ(M, U)), σ.app U s = baseSection f c U • s

/-- An endomorphism of an invertible sheaf is uniquely multiplication
by a base scalar when global functions equal the base ring. -/
public theorem existsUnique_isBaseScalar_of_isLineBundle_of_bijective
    (f : X ⟶ Spec (CommRingCat.of R))
    (hH0 : Function.Bijective fun c : R =>
      f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv c))
    {M : X.Modules} (hM : IsLineBundle M) (σ : M ⟶ M) :
    ∃! c : R, IsBaseScalar f σ c := by
  obtain ⟨s, hs, huniq⟩ := hM.existsUnique_app_eq_smul σ
  obtain ⟨c, hc⟩ := hH0.2 s
  simp only at hc
  refine ⟨c, ?_, ?_⟩
  · intro U x
    rw [hs U x]
    change _ = X.presheaf.map (homOfLE (le_top (a := U))).op
      (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv c)) • x
    rw [hc]
  · intro c' hc'
    have h1 : f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv c') = s :=
      huniq (f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv c'))
        (fun U x => hc' U x)
    apply hH0.1
    change f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv c') =
      f.appTop ((Scheme.ΓSpecIso (CommRingCat.of R)).inv c)
    rw [h1]
    exact hc.symm

end AlgebraicGeometry.DescentCharacter
