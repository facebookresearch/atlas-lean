/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.MotivicFinitePermutationModels

/-!
# The native associated permutation module

The module is an actual locally free sheaf on the original free quotient.
Its frame is on the pullback along the actual torsor projection. Descent
is fixed on every scheme-valued group element, including disconnected and
nonreduced tests: the original component idempotents weight the permutation
of the original free coordinates. No associated vector space or descent
equivalence is supplied independently of that formula.

Source: Voevodsky, arXiv:math/0107109v1, Construction 5.3. The left torsor
and left permutation actions use the same convention; a descended section
has coordinate v_j(gu) = v_{r(g)^{-1}j}(u).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.MotivicPermutationBundleModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open MotivicFinitePermutationModels GeneralMotivicBundleFrameMaps

variable {k H : Type} [Field k] [Group H]
  [C : ConstantGroupGeometry (k := k) (H := H)]

/-- An actual quotient module with its original torsor-pullback frame. -/
structure PermutationFrame (P : FreeQuotient (k := k) (H := H)) (n : ℕ) where
  module : P.base.scheme.left.Modules
  locallyFree : AlgebraicBundleGeometry.IsBundle module n
  frame : (Scheme.Modules.pullback P.projection.left).obj module ≅
    SheafOfModules.free (R := P.total.scheme.left.ringCatSheaf) (Fin n)

variable {P : FreeQuotient (k := k) (H := H)} {n : ℕ}

/-- Each coordinate is the actual pulled frame projection on the same module section. -/
def PermutationFrame.coordinate (E : PermutationFrame P n) (T : Over (Spec (.of k)))
    (u : T ⟶ P.total.scheme) (j : Fin n)
    (s : Γ((Scheme.Modules.pullback (u ≫ P.projection).left).obj E.module, ⊤)) :
    Γ(T.left, ⊤) :=
  (((((Scheme.Modules.pullbackComp u.left P.projection.left).inv.app E.module) ≫
    (Scheme.Modules.pullback u.left).map
      (E.frame.hom ≫ freeCoordinate P.total.scheme.left n j) ≫
    (AlgebraicBundleGeometry.pullbackUnit T.left P.total.scheme.left u.left).hom).val.app
      (op ⊤)).hom s)

/-- The section is transported along the proved equality of the original quotient maps. -/
def PermutationFrame.actionSection (E : PermutationFrame P n)
    (T : Over (Spec (.of k))) (g : T ⟶ constantScheme (k := k) (H := H))
    (u : T ⟶ P.total.scheme)
    (s : Γ((Scheme.Modules.pullback (u ≫ P.projection).left).obj E.module, ⊤)) :
    Γ((Scheme.Modules.pullback (P.actPoint T g u ≫ P.projection).left).obj E.module, ⊤) :=
  ((((Scheme.Modules.pullbackCongr
    (congrArg (fun a : T ⟶ P.base.scheme => a.left)
      (P.actPoint_projection T g u)).symm).hom.app E.module).val.app (op ⊤)).hom s)

/-- Full native linear descent, fixed on every group component and every section. -/
def PermutationFrame.IsDescent [Fintype H] (E : PermutationFrame P n)
    (r : H →* Equiv.Perm (Fin n)) : Prop :=
  ∀ (T : Over (Spec (.of k))) (g : T ⟶ constantScheme (k := k) (H := H))
    (u : T ⟶ P.total.scheme) (j : Fin n)
    (s : Γ((Scheme.Modules.pullback (u ≫ P.projection).left).obj E.module, ⊤)),
    E.coordinate T (P.actPoint T g u) j (E.actionSection T g u s) =
      ∑ h : H, componentCoordinate T g h * E.coordinate T u ((r h).symm j) s

/-- The associated module retains its prescribed representation descent as a source condition. -/
structure AssociatedPermutationModule [Fintype H]
    (P : FreeQuotient (k := k) (H := H)) (r : H →* Equiv.Perm (Fin n))
    extends PermutationFrame P n where
  descent : toPermutationFrame.IsDescent r

end MathlibExt.AlgebraicGeometry.MotivicPermutationBundleModels
