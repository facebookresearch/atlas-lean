/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.GraphClutchingModels
public import MathlibExt.AlgebraicGeometry.RelativeLambdaReindexing
public import MathlibExt.AlgebraicGeometry.StackFirstChernOperators

/-!
# Actual cotangent-line modules at stable-graph branches

The line at a marked branch is s*Omega1(C/T), for the actual vertex family
and its actual smooth marking. Its affine cartesian module is identified
with the sections of this literal pullback on every affine stack point.
Every restriction uses the same native curve/base map and the universal
relative differential. Zero sections and psi caps then use the native
stack first-Chern construction on this exact line.

Source: JPPZ arXiv:1602.04705v2, Section 0.3.3, printed p9.
Relative differentials/base-change producers are completed Mathlib/Stacks
source integration; their revision, Apache license and native generator
formulas are retained in RelativeDifferentialForms/RelativeLambdaReindexing.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section
  AlgebraicGeometry.SheafedSpace.sheaf

namespace MathlibExt.AlgebraicGeometry.GraphCotangentLines

open _root_.CategoryTheory _root_.CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open StableCurveStackModels StableGraphCurveGluing GraphClutchingModels
open StackCycleGeometry StackCycleRelations StackAffineModules StackVectorBundles
open StackChowGroups StackFirstChernOperators RelativeDifferentialForms RelativeLambdaReindexing

variable {k : Type} [Field k] {g n : ℕ}
  (M : StableCurveStackModel (k := k) g n)
  {X : Stack (Spec (.of k))} (p : StackHom X M.stack)

def cotangentModule (T : Over (Spec (.of k))) (x : X.Fibre T) (i : Fin n) : T.left.Modules :=
  (Scheme.Modules.pullback ((mappedFamilyAt M p T x).marking i)).obj
    (forms (mappedFamilyAt M p T x).π 1)

abbrev cotangentAt (a : AffinePoint X) (i : Fin n) :=
  cotangentModule M p a.obj.base a.obj.fiber i

local instance cotangentAtModule (a : AffinePoint X) (i : Fin n) :
    Module ((rings X).obj (op a)) Γ(cotangentAt M p a i, ⊤) :=
  inferInstanceAs (Module Γ(a.obj.base.left, ⊤) Γ(cotangentAt M p a i, ⊤))

/-- The exact relative affine generator comparison for the actual curve map. -/
structure OneFormReindex {a b : AffinePoint X} (f : a ⟶ b) where
  square : RelativeSquare (mappedFamilyAt M p b.obj.base b.obj.fiber).π
    (mappedFamilyAt M p a.obj.base a.obj.fiber).π
  total_eq : square.total = totalFamilyMap M p f.hom
  base_eq : square.base = f.hom.base.left
  one : (Scheme.Modules.pullback (totalFamilyMap M p f.hom)).obj
    (forms (mappedFamilyAt M p b.obj.base b.obj.fiber).π 1) ≅
      forms (mappedFamilyAt M p a.obj.base a.obj.fiber).π 1
  generators : ∀ (U : (mappedFamilyAt M p b.obj.base b.obj.fiber).X.Opens)
      (s : Γ((mappedFamilyAt M p b.obj.base b.obj.fiber).X, U)),
    (one.hom.val.app (op ((totalFamilyMap M p f.hom) ⁻¹ᵁ U))).hom
      (pullSection (totalFamilyMap M p f.hom)
        (forms (mappedFamilyAt M p b.obj.base b.obj.fiber).π 1) U
        ((d0 (mappedFamilyAt M p b.obj.base b.obj.fiber).π).d s)) =
      (d0 (mappedFamilyAt M p a.obj.base a.obj.fiber).π).d
        (((totalFamilyMap M p f.hom).app U).hom s)

/-- Pullback along the actual base and marking square, followed by the
same universal one-form comparison. -/
def cotangentPullbackIso {a b : AffinePoint X} (f : a ⟶ b)
    (R : OneFormReindex M p f) (i : Fin n) :
    (Scheme.Modules.pullback f.hom.base.left).obj (cotangentAt M p b i) ≅
      cotangentAt M p a i :=
  (Scheme.Modules.pullbackComp f.hom.base.left
      ((mappedFamilyAt M p b.obj.base b.obj.fiber).marking i)).app
        (forms (mappedFamilyAt M p b.obj.base b.obj.fiber).π 1) ≪≫
    (Scheme.Modules.pullbackCongr (totalFamilyMap_marking M p f.hom i).symm).app
      (forms (mappedFamilyAt M p b.obj.base b.obj.fiber).π 1) ≪≫
    ((Scheme.Modules.pullbackComp ((mappedFamilyAt M p a.obj.base a.obj.fiber).marking i)
      (totalFamilyMap M p f.hom)).app
        (forms (mappedFamilyAt M p b.obj.base b.obj.fiber).π 1)).symm ≪≫
    (Scheme.Modules.pullback ((mappedFamilyAt M p a.obj.base a.obj.fiber).marking i)).mapIso R.one

def cotangentRestriction {a b : AffinePoint X} (f : a ⟶ b)
    (R : OneFormReindex M p f) (i : Fin n) :
    Γ(cotangentAt M p b i, ⊤) →ₛₗ[f.hom.base.left.appTop.hom] Γ(cotangentAt M p a i, ⊤) where
  toFun s := ((cotangentPullbackIso M p f R i).hom.val.app (op ⊤)).hom
    (pullSection f.hom.base.left (cotangentAt M p b i) ⊤ s)
  map_add' s t := by rw [pullSection_add, map_add]
  map_smul' r s := by
    have h : pullSection f.hom.base.left (cotangentAt M p b i) ⊤ (r • s) =
        f.hom.base.left.appTop.hom r •
          pullSection f.hom.base.left (cotangentAt M p b i) ⊤ s :=
      ((((Scheme.Modules.pullbackPushforwardAdjunction f.hom.base.left).unit.app
        (cotangentAt M p b i)).val.app (op ⊤)).hom.map_smul r s)
    rw [h]
    exact ((cotangentPullbackIso M p f R i).hom.val.app (op ⊤)).hom.map_smul _ _

/-- A genuine line total-space whose cartesian module is the computed
cotangent module, on all objects and every source-normalized restriction. -/
structure CotangentLine (i : Fin n) where
  line : VectorBundle X
  rank_one : line.rank = 1
  reindex : ∀ {a b : AffinePoint X} (f : a ⟶ b), OneFormReindex M p f
  value : ∀ a : AffinePoint X,
    line.module.val.presheaf.obj (op a) ≃ₗ[(rings X).obj (op a)] Γ(cotangentAt M p a i, ⊤)
  naturality : ∀ {a b : AffinePoint X} (f : a ⟶ b)
      (s : line.module.val.presheaf.obj (op b)),
    value a (line.module.val.presheaf.restrictₛₗ f.op s) =
      cotangentRestriction M p f (reindex f) i (value b s)

end MathlibExt.AlgebraicGeometry.GraphCotangentLines
