/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RootEtaleRestrictions
public import MathlibExt.AlgebraicGeometry.SchemeStackModuleModels
public import MathlibExt.CategoryTheory.CanonicalAdjunctionBaseChange

/-!
# Source-normalized base change of a stack projection

The root restriction is literal native module precomposition. Scheme
pullback uses the actual sheaf-module pullback and the existing full
QCoh dictionaries. The pullback square is normalized on every affine
test, every module and every section by native pullback composition.
The direct-image comparison is its actual adjunction mate.

Source: Borne–Vistoli arXiv:1001.0466v2, Section6 and Theorem6.1.
The generic cartesian/QCoh adapters retain the AxiomMath/Stacks
c496df0d9beea9deaeabcea8492605f9a0a2313b Apache2.0 attribution.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option maxHeartbeats 400000
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.StackProjectionBaseChange

open _root_.CategoryTheory _root_.CategoryTheory.Functor _root_.Opposite _root_.AlgebraicGeometry
open _root_.AlgebraicGeometry.GeneralStackGeometry _root_.AlgebraicGeometry.StackFibreModels
open _root_.AlgebraicGeometry.StackCycleGeometry
open _root_.AlgebraicGeometry.StackAffineModules _root_.AlgebraicGeometry.CartesianStackModules
open _root_.AlgebraicGeometry.SchemeStackModuleModels

variable {X Y : Scheme.{0}} (f : Y ⟶ X)

/-- A proof about the fixed native pullback, independently of any root
or parabolic comparison theorem. -/
structure SchemePullbackLanding : Prop where
  quasicoherent : ∀ N : SchemeQCoh X,
    SheafOfModules.IsQuasicoherent (R := Y.ringCatSheaf)
      ((Scheme.Modules.pullback f).obj N.obj)

def schemePullback (H : SchemePullbackLanding f) : SchemeQCoh X ⥤ SchemeQCoh Y where
  obj N := ⟨(Scheme.Modules.pullback f).obj N.obj, H.quasicoherent N⟩
  map a := ObjectProperty.homMk ((Scheme.Modules.pullback f).map a.hom)
  map_id _ := by apply ObjectProperty.hom_ext; exact (Scheme.Modules.pullback f).map_id _
  map_comp _ _ := by apply ObjectProperty.hom_ext; exact (Scheme.Modules.pullback f).map_comp _ _

variable (R : RelativeStack X)
  [(RootEtaleRestrictions.pseudofunctor f R).IsStack (Scheme.fppfTopology.over Y)]
  (RY : RelativeStack Y) (hr : RY = RootEtaleRestrictions.stack f R)
  (S : SchemeStackModuleModels.Model (Over.mk (𝟙 X)))
  (T : SchemeStackModuleModels.Model (Over.mk (𝟙 Y)))
  (p : StackHom R S.stack) (q : StackHom RY T.stack)
  (K : ModuleDictionary S) (L : ModuleDictionary T) (H : SchemePullbackLanding f)

def rootRestriction : QCoh R ⥤ QCoh RY := by
  clear q
  subst RY
  exact RootEtaleRestrictions.restriction f R

def affineView : AffinePoint RY ⥤ AffinePoint R := by
  clear q
  subst RY
  exact RootEtaleRestrictions.affineView f R

theorem affineView_base (a : AffinePoint RY) :
    ((affineView f R RY hr).obj a).obj.base = (Over.map f).obj a.obj.base := by
  try clear q
  subst RY
  rfl

/-- Actual coefficient value of literal root restriction. -/
def restrictionValue (M : QCoh R) (a : AffinePoint RY)
    (x : ((rootRestriction f R RY hr).obj M).obj.obj (op a)) :
    M.obj.obj (op ((affineView f R RY hr).obj a)) := by
  try clear q
  subst RY
  exact x

def basePullback : QCoh S.stack ⥤ QCoh T.stack :=
  K.equivalence.functor ⋙ schemePullback f H ⋙ L.equivalence.inverse

/-- The scheme-module comparison is the native dictionary counit. -/
def baseModuleIso (N : QCoh S.stack) :
    L.toModules.obj ((basePullback f S T K L H).obj N) ≅
      (Scheme.Modules.pullback f).obj (K.toModules.obj N) :=
  (schemeQCohForget Y).mapIso
    (L.equivalence.counitIso.app ((schemePullback f H).obj (K.equivalence.functor.obj N)))

variable (hp : ∀ a : AffinePoint R, S.testMap ((affineMap p).obj a) = a.obj.base.hom)
  (hq : ∀ a : AffinePoint RY,
    T.testMap ((affineMap q).obj a) = a.obj.base.hom)

/-- All source coefficient values use the existing affine dictionary
and the actual projection test-map equality. -/
def sourceValue (N : QCoh S.stack) (a : AffinePoint RY)
    (x : (((pullback p) ⋙ rootRestriction f R RY hr).obj N).obj.obj (op a)) :
    Γ((Scheme.Modules.pullback (a.obj.base.hom ≫ f)).obj (K.toModules.obj N),⊤) := by
  clear hq q
  subst RY
  exact ((eqToHom (congrArg (fun g ↦ (Scheme.Modules.pullback g).obj (K.toModules.obj N))
      (hp ((RootEtaleRestrictions.affineView f R).obj a)))).val.app
        (op (⊤ : a.obj.base.left.Opens))).hom
    (K.sections N ((affineMap p).obj ((RootEtaleRestrictions.affineView f R).obj a)) x)

def targetValue (N : QCoh S.stack) (a : AffinePoint RY)
    (y : (((basePullback f S T K L H) ⋙ pullback q).obj N).obj.obj (op a)) :
    Γ((Scheme.Modules.pullback a.obj.base.hom).obj
      ((Scheme.Modules.pullback f).obj (K.toModules.obj N)),⊤) :=
  (((Scheme.Modules.pullback a.obj.base.hom).map
      (baseModuleIso f S T K L H N).hom).val.app (op (⊤ : a.obj.base.left.Opens))).hom
    (((eqToHom (congrArg
        (fun g ↦ (Scheme.Modules.pullback g).obj (L.toModules.obj ((basePullback f S T K L H).obj N)))
          (hq a))).val.app (op (⊤ : a.obj.base.left.Opens))).hom
      (L.sections ((basePullback f S T K L H).obj N) ((affineMap q).obj a) y))

/-- Base change for the projections $p : R \to X$ and $q : R_Y \to Y$, where $R_Y$ is the
restriction of $R$ along $f : Y \to X$, and $X$ and $Y$ are represented by the models $S$ and $T$,
whose quasi-coherent modules the dictionaries $K$ and $L$ identify with those on the schemes: a
natural isomorphism $\mathrm{res} \circ p^* \cong q^* \circ f^*$ of functors from quasi-coherent
modules on $X$ to quasi-coherent modules on $R_Y$, where $\mathrm{res}$ restricts modules from $R$
to $R_Y$ (`comparison`), which on sections is the canonical isomorphism
$(f \circ t)^* N \cong t^* f^* N$: for every quasi-coherent module $N$ on $X$, every affine point
of $R_Y$, with base map $t$ to $Y$, and every section $x$ over that point, the global section of
$t^* f^* N$ that `targetValue` attaches to the image of $x$ under the comparison is the image under
this isomorphism of the global section of $(f \circ t)^* N$ that `sourceValue` attaches to $x$
(`normalization`). -/
structure PullbackSquare where
  comparison : pullback p ⋙ rootRestriction f R RY hr ≅
    basePullback f S T K L H ⋙ pullback q
  normalization : ∀ (N : QCoh S.stack) (a : AffinePoint RY)
      (x : (((pullback p) ⋙ rootRestriction f R RY hr).obj N).obj.obj (op a)),
    targetValue f RY S T q K L H hq N a ((comparison.hom.app N).hom.app (op a) x) =
      (((Scheme.Modules.pullbackComp a.obj.base.hom f).inv.app (K.toModules.obj N)).val.app
        (op (⊤ : a.obj.base.left.Opens))).hom (sourceValue f R RY hr S p K hp N a x)

variable (Q : DirectImage p) (V : DirectImage q)
  (C : PullbackSquare f R RY hr S T p q K L H hp hq)

/-- The base-change map $f^* p_* \to q_* \,\mathrm{res}$, for right adjoints $p_*$ of $p^*$ and
$q_*$ of $q^*$ (`Q`, `V`): the mate of the inverse of the isomorphism
$\mathrm{res} \circ p^* \cong q^* \circ f^*$ of `C`, whose component at $M$ is the composite
$f^* p_* M \to q_* q^* f^* p_* M \cong q_* \mathrm{res}\, p^* p_* M \to q_* \mathrm{res}\, M$ of
the unit of $q^* \dashv q_*$, the inverse of that isomorphism, and the counit of
$p^* \dashv p_*$. -/
def directImageMap : Q.functor ⋙ basePullback f S T K L H ⟶
    rootRestriction f R RY hr ⋙ V.functor :=
  MathlibExt.CategoryTheory.CanonicalAdjunctionBaseChange.map Q.adjunction V.adjunction
    (basePullback f S T K L H) (rootRestriction f R RY hr) C.comparison

def moduleMap (M : QCoh R) :
    (Scheme.Modules.pullback f).obj (K.toModules.obj (Q.functor.obj M)) ⟶
      L.toModules.obj (V.functor.obj ((rootRestriction f R RY hr).obj M)) :=
  (baseModuleIso f S T K L H (Q.functor.obj M)).inv ≫
    L.toModules.map ((directImageMap f R RY hr S T p q K L H hp hq Q V C).app M)

end MathlibExt.AlgebraicGeometry.StackProjectionBaseChange
