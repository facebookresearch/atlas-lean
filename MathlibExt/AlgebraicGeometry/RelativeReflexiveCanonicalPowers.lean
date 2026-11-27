/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ModuleDerivedSquares
public import MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
public import MathlibExt.AlgebraicGeometry.LogPairs
public import MathlibExt.AlgebraicGeometry.QuasicoherentDualityReferences
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Actual relative reflexive canonical powers and base-change maps

For proper families, the canonical module and every power are the fixed
quasi-coherent H^(-n)(f!O) and
double dual of its actual tensor power. The canonical-module base-change
map is computed from the native derived-duality mate and normalized lowest
cohomology embedding, not freely supplied.

A reflexive-power extension is characterized by the exact biduality/power
diagram and its uniqueness. Kollár compatibility is a condition on those
fixed maps and the actual stalkwise relative flatness. It is not assumed
as a conclusion in a construction request.

Lowest-cohomology, biduality, derived existence and generic duality are
completed native/source integration inputs. Arbitrary singular-family
identification, log-boundary/conductor compatibility and a full provider
for every base change remain explicit dependencies; no CM or smoothness
is silently imposed on all slc families.

Source: Hacon--McKernan--Xu, arXiv1412.1186v2, §2.5;
Blum--Xu, arXiv1812.03538v2, Definition 2.1; Axiom finite/general duality
at c496df0d9beea9deaeabcea8492605f9a0a2313b, Apache 2.0.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RelativeReflexiveCanonicalPowers

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.Opposite
open MathlibExt.AlgebraicGeometry.FourierMukai
open MathlibExt.AlgebraicGeometry.BirationalDualityReferences
open MathlibExt.AlgebraicGeometry.ModuleDerivedSquares
open MathlibExt.AlgebraicGeometry.QuasicoherentDualityReferences
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
open MathlibExt.AlgebraicGeometry.ModuleInternalHom

attribute [local instance] HasDerivedCategory.standard

/-- Literal evaluation of the slice-wise native internal Hom at the terminal slice object. -/
def localHomValue (X : Scheme.{0}) (M N : X.Modules) (U : X.Opens)
    (φ : Γ(BundleTrace.homSheaf X M N, U)) (s : Γ(M, U)) : Γ(N, U) := by
  let φ' : (restrFun X.presheaf U).obj M.val ⟶ (restrFun X.presheaf U).obj N.val := φ
  exact (φ'.app (op (Over.mk (𝟙 U)))).hom s

/-- The biduality map of a sheaf of $\mathcal{O}_X$-modules $M$: a map $M \to M^{\vee\vee}$ to its
double dual, where $M^\vee$ (`dual M`) is the internal Hom into $\mathcal{O}_X$, sending each local
section $s \in M(U)$ to evaluation at $s$, that is, $(\mathrm{map}\,s)(b) = b(s)$ for every open $U$
and every $b \in M^\vee(U)$. -/
structure Biduality {X : Scheme.{0}} (M : X.Modules) where
  map : M ⟶ dual (dual M)
  normalized : ∀ (U : X.Opens) (s : Γ(M,U)) (b : Γ(dual M,U)),
    localHomValue X (dual M) (structureModule X) U ((map.app U) s) b =
      localHomValue X M (structureModule X) U b s

/-- Actual relative flatness on stalks, through the actual base stalk ring map. -/
def IsFlatOver {X S : Scheme.{0}} (f : X ⟶ S) (M : X.Modules) : Prop :=
  ∀ x : X,
    letI := LogPairs.moduleStalkModule X M x
    letI := Module.compHom (LogPairs.ModuleStalk X M x) (f.stalkMap x).hom
    Module.Flat (S.presheaf.stalk (f x)) (LogPairs.ModuleStalk X M x)

variable [HasDerivedPullbacks.{0}] [HasDerivedPushforwards.{0}]

/-- Native pullback of a single sheaf complex when its actual derived counit is invertible. -/
def singlePullbackIso {X Y : Scheme.{0}} (p : X ⟶ Y) (M : Y.Modules) (d : ℤ)
    (h : IsIso ((derivedPullbackCounit p).app
      ((CochainComplex.singleFunctor Y.Modules d).obj M))) :
    (derivedPullback p).obj ((DerivedCategory.singleFunctor Y.Modules d).obj M) ≅
      (DerivedCategory.singleFunctor X.Modules d).obj ((Scheme.Modules.pullback p).obj M) := by
  letI := h
  exact asIso ((derivedPullbackCounit p).app
    ((CochainComplex.singleFunctor Y.Modules d).obj M)) ≪≫
      DerivedCategory.Q.mapIso
        ((HomologicalComplex.singleMapHomologicalComplex
          (Scheme.Modules.pullback p) (.up ℤ) d).app M)

/-- Lowest-cohomology embedding into the fixed duality complex.
The actual t-structure bound makes its identity normalization canonical. -/
structure CanonicalEmbedding {X Y : Scheme.{0}} {f : X ⟶ Y}
    (P : ProperReference f) (n : ℕ) where
  [bounded : (properDuality P).IsGE (-(n : ℤ))]
  map : (DerivedCategory.singleFunctor X.Modules (-(n : ℤ))).obj
    (properCanonicalModule P n) ⟶ properDuality P
  normalized :
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso X.Modules (-(n : ℤ))).app
      (properCanonicalModule P n)).inv ≫
        (DerivedCategory.homologyFunctor X.Modules (-(n : ℤ))).map map =
          𝟙 (properCanonicalModule P n)

/-- Actual reflexive powers of the proper quasi-coherent canonical module. -/
def canonicalPower {X Y : Scheme.{0}} {f : X ⟶ Y} (P : ProperReference f) (n m : ℕ) :
    X.Modules := reflexivePower (properCanonicalModule P n) m

/-- Canonical-module base change from the fixed duality arrow and cohomology embedding. -/
def canonicalModuleMap {X' X Y' Y : Scheme.{0}}
    (p : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (comm : p ≫ f = f' ≫ g) (P : ProperReference f) (P' : ProperReference f')
    (AF : PullPushAdjunction f)
    (AF' : PullPushAdjunction f') (A : PullbackPasting f' g) (B : PullbackPasting p f)
    (U : UnitPullback g) (n : ℕ)
    (C : CanonicalEmbedding P n)
    (hL : quasicoherent X' ((derivedPullback p).obj (properDuality P)))
    (hbase : IsIso (baseChangeMap p f' f g comm AF AF' A B (properDuality P)))
    (hsingle : IsIso ((derivedPullbackCounit p).app
      ((CochainComplex.singleFunctor X.Modules (-(n : ℤ))).obj
        (properCanonicalModule P n)))) :
    (Scheme.Modules.pullback p).obj (properCanonicalModule P n) ⟶
      properCanonicalModule P' n :=
  ((DerivedCategory.singleFunctorCompHomologyFunctorIso X'.Modules (-(n : ℤ))).app
    ((Scheme.Modules.pullback p).obj (properCanonicalModule P n))).inv ≫
  (DerivedCategory.homologyFunctor X'.Modules (-(n : ℤ))).map
    ((singlePullbackIso p (properCanonicalModule P n) (-(n : ℤ)) hsingle).inv ≫
      (derivedPullback p).map C.map ≫
        properBaseChange p f' f g comm P P' AF AF' A B U hL hbase)

/-- Exact and uniquely normalized extension to the actual reflexive tensor powers.
This records a construction boundary, not a freely chosen base-change operator. -/
structure ReflexivePowerExtension {X' X : Scheme.{0}} (p : X' ⟶ X)
    (M : X.Modules) (N : X'.Modules)
    (α : (Scheme.Modules.pullback p).obj M ⟶ N) (P : PullbackPowers p) (m : ℕ)
    (E : Biduality (power M m)) (E' : Biduality (power N m)) where
  map : (Scheme.Modules.pullback p).obj (reflexivePower M m) ⟶ reflexivePower N m
  normalized : (Scheme.Modules.pullback p).map E.map ≫ map =
    (P.comparison m).hom.app M ≫ powerMap α m ≫ E'.map
  unique : ∀ φ : (Scheme.Modules.pullback p).obj (reflexivePower M m) ⟶ reflexivePower N m,
    (Scheme.Modules.pullback p).map E.map ≫ φ =
      (P.comparison m).hom.app M ≫ powerMap α m ≫ E'.map → φ = map

/-- For one supplied comparison map `α` (not necessarily the canonical base-change
map) and one square: every reflexive canonical power is flat over `Y`, and every
induced extension of `α` to the reflexive powers is an isomorphism. This tests the
supplied `α` only. Kollár's condition is this test for the canonical base-change
map at every cartesian base change. -/
def FlatPowersAndIsoAt {X' X Y' Y : Scheme.{0}}
    (p : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y)
    (R : ProperReference f) (R' : ProperReference f')
    (n : ℕ) (α : (Scheme.Modules.pullback p).obj (properCanonicalModule R n) ⟶
      properCanonicalModule R' n) (P : PullbackPowers p)
    (E : ∀ m, Biduality (power (properCanonicalModule R n) m))
    (E' : ∀ m, Biduality (power (properCanonicalModule R' n) m))
    (B : ∀ m, ReflexivePowerExtension p (properCanonicalModule R n)
      (properCanonicalModule R' n) α P m (E m) (E' m)) : Prop :=
  ∀ m : ℕ, IsFlatOver f (canonicalPower R n m) ∧ IsIso (B m).map


/-- Native extension across an open from the actual target Hartogs unit and invertible local
source map. Every map is computed by the ordinary pullback/pushforward adjunction. -/
def extendAcrossOpen {X : Scheme.{0}} (U : X.Opens) {A M N : X.Modules}
    (e : A ⟶ M) (β : A ⟶ N)
    (hE : IsIso ((Scheme.Modules.pullback U.ι).map e))
    (hN : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app N)) :
    {φ : M ⟶ N // e ≫ φ = β ∧ ∀ φ' : M ⟶ N, e ≫ φ' = β → φ' = φ} := by
  letI := hE
  letI := hN
  let L := Scheme.Modules.pullback U.ι
  let R := Scheme.Modules.pushforward U.ι
  let adj := Scheme.Modules.pullbackPushforwardAdjunction U.ι
  have hn {B C : X.Modules} (a : B ⟶ C) :
      a ≫ adj.unit.app C = adj.unit.app B ≫ R.map (L.map a) := by
    simpa only [Functor.id_map, Functor.comp_map] using adj.unit.naturality a
  let ψ : L.obj M ⟶ L.obj N := inv (L.map e) ≫ L.map β
  let φ : M ⟶ N := adj.unit.app M ≫ R.map ψ ≫ inv (adj.unit.app N)
  have heψ : L.map e ≫ ψ = L.map β := by
    simp only [ψ, ← Category.assoc, IsIso.hom_inv_id, Category.id_comp]
  have heφ : e ≫ φ = β := by
    calc
      e ≫ φ = (e ≫ adj.unit.app M) ≫ R.map ψ ≫ inv (adj.unit.app N) := by
        simp only [φ, Category.assoc]
      _ = (adj.unit.app A ≫ R.map (L.map e)) ≫ R.map ψ ≫ inv (adj.unit.app N) := by
        rw [hn e]
      _ = adj.unit.app A ≫ R.map (L.map e ≫ ψ) ≫ inv (adj.unit.app N) := by
        simp only [Functor.map_comp, Category.assoc]
      _ = adj.unit.app A ≫ R.map (L.map β) ≫ inv (adj.unit.app N) := by rw [heψ]
      _ = (β ≫ adj.unit.app N) ≫ inv (adj.unit.app N) := by
        rw [hn β]
        simp only [Category.assoc]
      _ = β := by simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  refine ⟨φ, heφ, ?_⟩
  intro φ' hφ'
  have hψ : L.map φ' = ψ := by
    calc
      L.map φ' = inv (L.map e) ≫ (L.map e ≫ L.map φ') := by
        simp only [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
      _ = inv (L.map e) ≫ L.map β := by rw [← L.map_comp, hφ']
      _ = ψ := rfl
  calc
    φ' = (φ' ≫ adj.unit.app N) ≫ inv (adj.unit.app N) := by
      simp only [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    _ = (adj.unit.app M ≫ R.map (L.map φ')) ≫ inv (adj.unit.app N) := by
      rw [hn φ']
    _ = φ := by rw [hψ]; rfl

/-- Completed formal construction of the uniquely normalized reflexive-power comparison.
The target Hartogs unit and the local biduality isomorphism are actual geometric/source inputs,
not an assumed global comparison or Kollár compatibility conclusion. -/
def reflexivePowerAcrossOpen {X' X : Scheme.{0}} (p : X' ⟶ X)
    (M : X.Modules) (N : X'.Modules)
    (α : (Scheme.Modules.pullback p).obj M ⟶ N) (P : PullbackPowers p) (m : ℕ)
    (E : Biduality (power M m)) (E' : Biduality (power N m)) (U : X'.Opens)
    (hE : IsIso ((Scheme.Modules.pullback U.ι).map ((Scheme.Modules.pullback p).map E.map)))
    (hN : IsIso ((Scheme.Modules.pullbackPushforwardAdjunction U.ι).unit.app
      (reflexivePower N m))) :
    ReflexivePowerExtension p M N α P m E E' :=
  let φ := extendAcrossOpen U ((Scheme.Modules.pullback p).map E.map)
    ((P.comparison m).hom.app M ≫ powerMap α m ≫ E'.map) hE hN
  { map := φ.val
    normalized := φ.property.1
    unique := φ.property.2 }

end MathlibExt.AlgebraicGeometry.RelativeReflexiveCanonicalPowers
