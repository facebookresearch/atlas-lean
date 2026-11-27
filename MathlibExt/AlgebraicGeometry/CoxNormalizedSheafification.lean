/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CoxGradedSheaves
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Character-normalized Cox chart modules and sheafification

The comparison sends every semigroup character to its literal homogeneous
polynomial fraction. Local modules and their maps are actual localized
degree-zero modules, followed by Mathlib's tilde and scheme pushforward.
A global comparison is pinned on the whole affine cover, including maps.
Neither Cartier invertibility nor geometric quotient is asserted for a
general fan. Quasicoherent essential surjectivity has the simplicial scope
of Cox, alg-geom/9210008v3, Proposition 3.1 and Theorem 3.2.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CoxNormalizedSheafification

open CategoryTheory _root_.AlgebraicGeometry FiniteToricCoordinates CoxGradedSheaves
open scoped BigOperators

variable {n : ℕ} {F : FiniteFan n} (R : Rays F)

def rayPairing (u : Lattice n) (i : Fin R.count) : ℤ :=
  ∑ j, u j * R.generator i j

def AdmissiblePower (σ : Cone n) (u : Lattice n) (a : ℕ) : Prop := by
  classical
  exact ∀ i, 0 ≤ rayPairing R u i + if rayInCone R σ i then 0 else (a : ℤ)

def characterNumerator (σ : Cone n) (u : Lattice n) (a : ℕ) : CoxRing R := by
  classical
  exact MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm fun i ↦
    (rayPairing R u i + if rayInCone R σ i then 0 else (a : ℤ)).toNat) 1

/-- A comparison is determined on every character, for every admissible
denominator exponent. It is not an unconstrained chart algebra. -/
structure ChartComparison where
  iso : ∀ σ : F.Face, CoordinateRing ℂ σ.val ≃ₐ[ℂ] degreeZeroAlgebra R σ.val
  character : ∀ (σ : F.Face) (u : dualSemigroup σ.val) (a : ℕ),
    AdmissiblePower R σ.val u.val a →
      ((iso σ (AddMonoidAlgebra.single u 1)).val : LocalRing R σ.val) =
        Localization.mk (characterNumerator R σ.val u.val a) (denominatorPower R σ.val a)

def localizedMap {M N : GradedModule R} (σ : Cone n) (f : M ⟶ N) :
    LocalModule R σ M →ₗ[degreeZeroAlgebra R σ] LocalModule R σ N where
  toFun := LocalizedModule.map (Submonoid.powers (denominator R σ)) f.map
  map_add' := map_add _
  map_smul' c x := by
    change (LocalizedModule.map (Submonoid.powers (denominator R σ)) f.map) (c.val • x) =
      c.val • (LocalizedModule.map (Submonoid.powers (denominator R σ)) f.map) x
    exact map_smul _ c.val x

def degreeZeroMap {M N : GradedModule R} (σ : Cone n) (f : M ⟶ N) :
    degreeZeroModule R σ M →ₗ[degreeZeroAlgebra R σ] degreeZeroModule R σ N :=
  (localizedMap R σ f).restrict (by
    have h : degreeZeroModule R σ M ≤
        (degreeZeroModule R σ N).comap (localizedMap R σ f) := by
      apply Submodule.span_le.mpr
      rintro x ⟨a, m, hm, rfl⟩
      apply Submodule.subset_span
      refine ⟨a, f.map m, f.graded _ m hm, ?_⟩
      exact LocalizedModule.map_mk _ _ _ _
    exact fun _ hx ↦ h hx)

/-- Tilde on the literal localized degree-zero module. -/
def localSheaf (C : ChartComparison R) (σ : F.Face) (M : GradedModule R) :
    (affineChart ℂ σ.val).left.Modules :=
  (Scheme.Modules.pushforward (Spec.map
    (CommRingCat.ofHom (C.iso σ).toRingHom))).obj
      (tilde (ModuleCat.of (degreeZeroAlgebra R σ.val) (degreeZeroModule R σ.val M)))

def localSheafMap (C : ChartComparison R) (σ : F.Face)
    {M N : GradedModule R} (f : M ⟶ N) : localSheaf R C σ M ⟶ localSheaf R C σ N :=
  (Scheme.Modules.pushforward (Spec.map
    (CommRingCat.ofHom (C.iso σ).toRingHom))).map
      (tilde.map (ModuleCat.ofHom (degreeZeroMap R σ.val f)))

def localSection (C : ChartComparison R) (σ : F.Face) (M : GradedModule R)
    (m : degreeZeroModule R σ.val M) : Γ(localSheaf R C σ M, ⊤) :=
  (tilde.toOpen (R := CommRingCat.of (degreeZeroAlgebra R σ.val))
    (ModuleCat.of (degreeZeroAlgebra R σ.val)
    (degreeZeroModule R σ.val M)) ⊤).hom m

/-- Every localization map is fixed on the original Cox coefficients and
module elements. The affine sheaf comparison is fixed on every global
module generator through the actual pullback/pushforward adjunction unit. -/
structure FaceComparison (C : ChartComparison R) (σ τ : F.Face)
    (h : τ.val.IsFaceOf σ.val) where
  ringMap : LocalRing R σ.val →+* LocalRing R τ.val
  coefficient : ∀ p : CoxRing R,
    ringMap (algebraMap (CoxRing R) (LocalRing R σ.val) p) =
      algebraMap (CoxRing R) (LocalRing R τ.val) p
  moduleMap : ∀ M : GradedModule R,
    LocalModule R σ.val M →ₛₗ[ringMap] LocalModule R τ.val M
  unit : ∀ (M : GradedModule R) (m : M.object),
    moduleMap M (LocalizedModule.mk m 1) = LocalizedModule.mk m 1
  degreeZero : ∀ (M : GradedModule R) (m : degreeZeroModule R σ.val M),
    moduleMap M m.val ∈ degreeZeroModule R τ.val M
  iso : ∀ M : GradedModule R,
    (Scheme.Modules.pullback (faceMap ℂ h).left).obj (localSheaf R C σ M) ≅
      localSheaf R C τ M
  normalized : ∀ (M : GradedModule R) (m : degreeZeroModule R σ.val M),
    ((Scheme.Modules.pullbackPushforwardAdjunction (faceMap ℂ h).left).unit.app
        (localSheaf R C σ M) ≫
      (Scheme.Modules.pushforward (faceMap ℂ h).left).map (iso M).hom).app ⊤
        (localSection R C σ M m) =
      localSection R C τ M ⟨moduleMap M m.val, degreeZero M m⟩

def globalFaceIso (T : Realization ℂ F) (σ τ : F.Face) (h : τ.val.IsFaceOf σ.val)
    (M : T.scheme.left.Modules) :
    (Scheme.Modules.pullback (faceMap ℂ h).left).obj
      ((Scheme.Modules.pullback (T.chartMap σ).left).obj M) ≅
        (Scheme.Modules.pullback (T.chartMap τ).left).obj M :=
  (Scheme.Modules.pullbackComp (faceMap ℂ h).left (T.chartMap σ).left).app M ≪≫
    (Scheme.Modules.pullbackCongr
      (congrArg (fun f : affineChart ℂ τ.val ⟶ T.scheme ↦ f.left)
        (T.face_naturality σ τ h))).app M

/-- Sheafification of graded modules over the Cox ring on a given realization $T$ of the fan over
$ℂ$, for a given chart comparison $C$: a functor from graded modules to sheaves of modules on $T$,
with quasi-coherent values, together with isomorphisms, natural in the module, from its
restriction to the affine chart of each cone $σ$ of the fan to `localSheaf` (the sheaf of the
degree-zero part of the localized module), and face comparisons (`FaceComparison`) for each face
$τ$ of $σ$, compatible with these isomorphisms. -/
structure Sheafification (C : ChartComparison R) (T : Realization ℂ F) where
  functor : GradedModule R ⥤ T.scheme.left.Modules
  localIso : ∀ (σ : F.Face) (M : GradedModule R),
    (Scheme.Modules.pullback (T.chartMap σ).left).obj (functor.obj M) ≅ localSheaf R C σ M
  local_maps : ∀ (σ : F.Face) {M N : GradedModule R} (f : M ⟶ N),
    (Scheme.Modules.pullback (T.chartMap σ).left).map (functor.map f) ≫ (localIso σ N).hom =
      (localIso σ M).hom ≫ localSheafMap R C σ f
  faceComparison : ∀ (σ τ : F.Face) (h : τ.val.IsFaceOf σ.val), FaceComparison R C σ τ h
  face_compatibility : ∀ (σ τ : F.Face) (h : τ.val.IsFaceOf σ.val) (M : GradedModule R),
    (Scheme.Modules.pullback (faceMap ℂ h).left).map (localIso σ M).hom ≫
      ((faceComparison σ τ h).iso M).hom =
        (globalFaceIso T σ τ h (functor.obj M)).hom ≫ (localIso τ M).hom
  quasicoherent : ∀ M, (functor.obj M).IsQuasicoherent

def IsSimplicial : Prop :=
  ∀ σ : F.Face, LinearIndependent ℝ
    (fun i : {i : Fin R.count // rayInCone R σ.val i} ↦ latticeCast n (R.generator i.val))

end MathlibExt.AlgebraicGeometry.CoxNormalizedSheafification
