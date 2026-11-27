/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralRamificationSymbols
public import MathlibExt.AlgebraicGeometry.LineBundleTaskContracts
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Full native reindexing of ramification symbols

Coefficient maps send every b tensor {g} to f(b) tensor {f(g)}. The
sheaf map is normalized on every actual tilde section, using the native
pullback of a section. Presentations of the global ideal-symbol line
commute with these actual maps on every affine chart arrow. Thus
nilpotent automorphisms invisible to ideal evaluation are not used as
independently chosen transition maps.
Source: Donagi--Gaitsgory arXiv:math/0005132v3, Section5.2.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.CameralSymbolReindexModels

open _root_.CategoryTheory _root_.AlgebraicGeometry
open CameralRamificationSymbols LineBundleTaskContracts
open scoped TensorProduct

variable {k : Type} [Field k]
  {B B' : Type} [CommRing B] [Algebra k B] [CommRing B'] [Algebra k B']
  {s : B ≃ₐ[k] B} {s' : B' ≃ₐ[k] B'}

structure CoefficientMap (f : B →ₐ[k] B') where
  commutes : ∀ b : B, s' (f b) = f (s b)
  map : symbols B s →ₛₗ[f.toRingHom] symbols B' s'
  pure : ∀ (b : B) (g : antiInvariant B s),
    map (b ⊗ₜ[invariantAlgebra B s] g) =
      f b ⊗ₜ[invariantAlgebra B' s']
        (⟨f g.val, by
          change s' (f g.val) = -(f g.val)
          rw [commutes, g.property, map_neg]⟩ : antiInvariant B' s')

def symbolSheaf (B : Type) [CommRing B] [Algebra k B] (s : B ≃ₐ[k] B) :
    (Spec (.of B)).Modules :=
  (tilde.functor (.of B)).obj (ModuleCat.of B (symbols B s))

def symbolSection (e : symbols B s) : Section (symbolSheaf B s) :=
  (tildeSelf (R := .of B)).inv ≫
    (tilde.functor (.of B)).map
      (ModuleCat.ofHom (LinearMap.toSpanSingleton B (symbols B s) e))

structure SheafMap (f : B →ₐ[k] B') (C : CoefficientMap (s := s) (s' := s') f) where
  map : (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom f.toRingHom))).obj
    (symbolSheaf B s) ⟶ symbolSheaf B' s'
  normalized : ∀ e : symbols B s,
    pullbackSection (Spec.map (CommRingCat.ofHom f.toRingHom)) (symbolSection e) ≫ map =
      symbolSection (C.map e)

variable {Y : Over (Spec (.of k))} {a : Y.left ≅ Y.left}

structure ChartArrow (U U' : AffineReflection Y a) where
  coefficients : U.algebra →ₐ[k] U'.algebra
  symbols : CoefficientMap (s := U.reflection) (s' := U'.reflection) coefficients
  sheaf : SheafMap coefficients symbols
  geometric : Spec.map (CommRingCat.ofHom coefficients.toRingHom) ≫
    U.chart.hom ≫ U.neighborhood.val.ι = U'.chart.hom ≫ U'.neighborhood.val.ι

structure GlobalPresentation (I : IdealSymbols Y a) where
  presentation : ∀ U : AffineReflection Y a,
    (Scheme.Modules.pullback (U.chart.hom ≫ U.neighborhood.val.ι)).obj I.module ≅
      symbolSheaf U.algebra U.reflection
  coefficients : ∀ (U : AffineReflection Y a) (e : symbols U.algebra U.reflection),
    (((moduleSpecΓFunctor (R := .of U.algebra)).map (presentation U).hom).hom
      ((I.symbolSections U).inv.hom e)) =
      (((tilde.adjunction (R := .of U.algebra)).unit.app
        (ModuleCat.of U.algebra (symbols U.algebra U.reflection))).hom e)
  naturality : ∀ {U U' : AffineReflection Y a} (f : ChartArrow U U'),
    (Scheme.Modules.pullback (Spec.map (CommRingCat.ofHom f.coefficients.toRingHom))).map
      (presentation U).hom ≫ f.sheaf.map =
      (Scheme.Modules.pullbackComp
        (Spec.map (CommRingCat.ofHom f.coefficients.toRingHom))
        (U.chart.hom ≫ U.neighborhood.val.ι)).hom.app I.module ≫
      (Scheme.Modules.pullbackCongr
        (by simpa only [Category.assoc] using f.geometric)).hom.app I.module ≫
      (presentation U').hom

end MathlibExt.AlgebraicGeometry.CameralSymbolReindexModels
