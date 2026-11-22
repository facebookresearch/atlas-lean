/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
See NOTICE in the repository root for the original attribution.
-/

import MathlibExt.Algebra.Category.Grp.RepresentedFiveLemma
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.NativeOmegaHoHomGroups

/-!
# Full native Omega-target Hom Five Lemma

The three middle source Hom sets are typed through their complete
original represented groups. The actual outer connecting functions remain
arbitrary, with all six exactness laws and four source squares. The
original orthogonal Omega condition constructs the required groups.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra MonoidalCategory
open CategoryTheory.EnrichedFunctorCat
open scoped CGWH.modelCategory ZeroObject

namespace PointedCGWH.Spectra.Orthogonal.OriginalOmegaHoHomGroup.Generic

attribute [local instance] PointedCGWH.copowerUnderlyingEnrichedOrdinary
  PointedCGWH.copowerUnderlyingMonoidal

private abbrev V := PointedCGWH.{u, v}
variable {I : Type} [EnrichedCategory V.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

private abbrev C := EnrichedFunctorCat V.{u, v} I
private abbrev H := toHomotopyCategory (C.{u, v} (I := I))
private instance nativeZero : HasZeroObject (C.{u, v} (I := I)) :=
  HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.nativeHasZeroObject

/-- A full original Hom ladder to a genuine loop target is a group Five Lemma
on its three middle terms; the actual outside functions remain arbitrary. -/
private theorem nativeHomFiveLemmaWithGroups
    {A A' Z Z' : Type*}
    {XB XC XD XB' XC' XD' : C.{u, v} (I := I)}
    (E : C.{u, v} (I := I)) (groups : SourceHomGroups E)
    (l : A → (H.obj XB ⟶ H.obj E)) (m : XC ⟶ XB) (n : XD ⟶ XC)
    (r : (H.obj XD ⟶ H.obj E) → Z)
    (l' : A' → (H.obj XB' ⟶ H.obj E)) (m' : XC' ⟶ XB') (n' : XD' ⟶ XC')
    (r' : (H.obj XD' ⟶ H.obj E) → Z')
    (a : A → A') (b : XB' ⟶ XB) (c : XC' ⟶ XC) (d : XD' ⟶ XD) (e : Z → Z')
    (z : Z) (z' : Z')
    (hl : ∀ x, (∃ y, l y = x) ↔ H.map m ≫ x = OrdinaryHoCofiberKernel.nullHom XC E)
    (hm : ∀ x, (∃ y, H.map m ≫ y = x) ↔ H.map n ≫ x = OrdinaryHoCofiberKernel.nullHom XD E)
    (hn : ∀ x, (∃ y, H.map n ≫ y = x) ↔ r x = z)
    (hl' : ∀ x, (∃ y, l' y = x) ↔ H.map m' ≫ x = OrdinaryHoCofiberKernel.nullHom XC' E)
    (hm' : ∀ x, (∃ y, H.map m' ≫ y = x) ↔ H.map n' ≫ x = OrdinaryHoCofiberKernel.nullHom XD' E)
    (hn' : ∀ x, (∃ y, H.map n' ≫ y = x) ↔ r' x = z')
    (hab : ∀ x, H.map b ≫ l x = l' (a x))
    (hbc : ∀ x : H.obj XB ⟶ H.obj E, H.map c ≫ (H.map m ≫ x) = H.map m' ≫ (H.map b ≫ x))
    (hcd : ∀ x : H.obj XC ⟶ H.obj E, H.map d ≫ (H.map n ≫ x) = H.map n' ≫ (H.map c ≫ x))
    (hde : ∀ x, e (r x) = r' (H.map d ≫ x))
    (hz : e z = z')
    (ha : Function.Surjective a)
    (hb : Function.Bijective (fun x : H.obj XB ⟶ H.obj E => H.map b ≫ x))
    (hd : Function.Bijective (fun x : H.obj XD ⟶ H.obj E => H.map d ≫ x))
    (he : Function.Injective e) :
    Function.Bijective (fun x : H.obj XC ⟶ H.obj E => H.map c ≫ x) := by
  exact GrpCat.RepresentedFiveLemma.bundledFiveLemma
    (groups.obj XB) (groups.obj XC) (groups.obj XD)
    (groups.obj XB') (groups.obj XC') (groups.obj XD')
    (groups.equiv XB) (groups.equiv XC) (groups.equiv XD)
    (groups.equiv XB') (groups.equiv XC') (groups.equiv XD')
    l (fun x => H.map m ≫ x) (fun x => H.map n ≫ x) r
    l' (fun x => H.map m' ≫ x) (fun x => H.map n' ≫ x) r'
    a (fun x => H.map b ≫ x) (fun x => H.map c ≫ x) (fun x => H.map d ≫ x) e
    (groups.map m).hom (groups.map n).hom (groups.map m').hom (groups.map n').hom
    (groups.map b).hom (groups.map c).hom (groups.map d).hom
    (OrdinaryHoCofiberKernel.nullHom XC E) (OrdinaryHoCofiberKernel.nullHom XD E) z
    (OrdinaryHoCofiberKernel.nullHom XC' E) (OrdinaryHoCofiberKernel.nullHom XD' E) z'
    (groups.null XC) (groups.null XD) (groups.null XC') (groups.null XD')
    (groups.naturality m) (groups.naturality n) (groups.naturality m') (groups.naturality n')
    (groups.naturality b) (groups.naturality c) (groups.naturality d)
    hl hm hn hl' hm' hn' hab hbc hcd hde hz ha hb hd he

/-- A full original Hom ladder to a genuine loop target is a group Five Lemma
on its three middle terms; the actual outside functions remain arbitrary. -/
theorem nativeHomFiveLemma
    {A A' Z Z' : Type*}
    {XB XC XD XB' XC' XD' : C.{u, v} (I := I)}
    (E D : C.{u, v} (I := I))
    (eLoop : H.obj E ≅ H.obj ((cotensor PointedCGWH.sphereOne).obj D))
    (l : A → (H.obj XB ⟶ H.obj E)) (m : XC ⟶ XB) (n : XD ⟶ XC)
    (r : (H.obj XD ⟶ H.obj E) → Z)
    (l' : A' → (H.obj XB' ⟶ H.obj E)) (m' : XC' ⟶ XB') (n' : XD' ⟶ XC')
    (r' : (H.obj XD' ⟶ H.obj E) → Z')
    (a : A → A') (b : XB' ⟶ XB) (c : XC' ⟶ XC) (d : XD' ⟶ XD) (e : Z → Z')
    (z : Z) (z' : Z')
    (hl : ∀ x, (∃ y, l y = x) ↔ H.map m ≫ x = OrdinaryHoCofiberKernel.nullHom XC E)
    (hm : ∀ x, (∃ y, H.map m ≫ y = x) ↔ H.map n ≫ x = OrdinaryHoCofiberKernel.nullHom XD E)
    (hn : ∀ x, (∃ y, H.map n ≫ y = x) ↔ r x = z)
    (hl' : ∀ x, (∃ y, l' y = x) ↔ H.map m' ≫ x = OrdinaryHoCofiberKernel.nullHom XC' E)
    (hm' : ∀ x, (∃ y, H.map m' ≫ y = x) ↔ H.map n' ≫ x = OrdinaryHoCofiberKernel.nullHom XD' E)
    (hn' : ∀ x, (∃ y, H.map n' ≫ y = x) ↔ r' x = z')
    (hab : ∀ x, H.map b ≫ l x = l' (a x))
    (hbc : ∀ x : H.obj XB ⟶ H.obj E, H.map c ≫ (H.map m ≫ x) = H.map m' ≫ (H.map b ≫ x))
    (hcd : ∀ x : H.obj XC ⟶ H.obj E, H.map d ≫ (H.map n ≫ x) = H.map n' ≫ (H.map c ≫ x))
    (hde : ∀ x, e (r x) = r' (H.map d ≫ x))
    (hz : e z = z')
    (ha : Function.Surjective a)
    (hb : Function.Bijective (fun x : H.obj XB ⟶ H.obj E => H.map b ≫ x))
    (hd : Function.Bijective (fun x : H.obj XD ⟶ H.obj E => H.map d ≫ x))
    (he : Function.Injective e) :
    Function.Bijective (fun x : H.obj XC ⟶ H.obj E => H.map c ≫ x) := by
  exact nativeHomFiveLemmaWithGroups E (sourceHomGroups E D eLoop)
    l m n r l' m' n' r' a b c d e z z'
    hl hm hn hl' hm' hn' hab hbc hcd hde hz ha hb hd he


end PointedCGWH.Spectra.Orthogonal.OriginalOmegaHoHomGroup.Generic

namespace PointedCGWH.Spectra.Orthogonal.OriginalOmegaHoHomGroup

attribute [local instance] PointedCGWH.copowerUnderlyingEnrichedOrdinary
  PointedCGWH.copowerUnderlyingMonoidal

private abbrev O := CategoryTheory.Spectra.OrthogonalOperatorIndex.{u, v}
private abbrev C :=
  HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual.OrthogonalCarrier.{u, v}
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
private abbrev H := toHomotopyCategory C.{u, v}
private instance nativeZero : HasZeroObject C.{u, v} :=
  HomotopicalAlgebra.EnrichedProjective.Native.Diagrams.nativeHasZeroObject

/-- A full original Hom ladder to a genuine loop target is a group Five Lemma
on its three middle terms; the actual outside functions remain arbitrary. -/
theorem omegaHomFiveLemma
    {A A' Z Z' : Type*}
    {XB XC XD XB' XC' XD' : C.{u, v}}
    (E : C.{u, v})
    (hE : HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.NativeK.IsOmega
      HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual.orthogonalFamily E)
    (l : A → (H.obj XB ⟶ H.obj E)) (m : XC ⟶ XB) (n : XD ⟶ XC)
    (r : (H.obj XD ⟶ H.obj E) → Z)
    (l' : A' → (H.obj XB' ⟶ H.obj E)) (m' : XC' ⟶ XB') (n' : XD' ⟶ XC')
    (r' : (H.obj XD' ⟶ H.obj E) → Z')
    (a : A → A') (b : XB' ⟶ XB) (c : XC' ⟶ XC) (d : XD' ⟶ XD) (e : Z → Z')
    (z : Z) (z' : Z')
    (hl : ∀ x, (∃ y, l y = x) ↔ H.map m ≫ x = OrdinaryHoCofiberKernel.nullHom XC E)
    (hm : ∀ x, (∃ y, H.map m ≫ y = x) ↔ H.map n ≫ x = OrdinaryHoCofiberKernel.nullHom XD E)
    (hn : ∀ x, (∃ y, H.map n ≫ y = x) ↔ r x = z)
    (hl' : ∀ x, (∃ y, l' y = x) ↔ H.map m' ≫ x = OrdinaryHoCofiberKernel.nullHom XC' E)
    (hm' : ∀ x, (∃ y, H.map m' ≫ y = x) ↔ H.map n' ≫ x = OrdinaryHoCofiberKernel.nullHom XD' E)
    (hn' : ∀ x, (∃ y, H.map n' ≫ y = x) ↔ r' x = z')
    (hab : ∀ x, H.map b ≫ l x = l' (a x))
    (hbc : ∀ x : H.obj XB ⟶ H.obj E, H.map c ≫ (H.map m ≫ x) = H.map m' ≫ (H.map b ≫ x))
    (hcd : ∀ x : H.obj XC ⟶ H.obj E, H.map d ≫ (H.map n ≫ x) = H.map n' ≫ (H.map c ≫ x))
    (hde : ∀ x, e (r x) = r' (H.map d ≫ x))
    (hz : e z = z')
    (ha : Function.Surjective a)
    (hb : Function.Bijective (fun x : H.obj XB ⟶ H.obj E => H.map b ≫ x))
    (hd : Function.Bijective (fun x : H.obj XD ⟶ H.obj E => H.map d ≫ x))
    (he : Function.Injective e) :
    Function.Bijective (fun x : H.obj XC ⟶ H.obj E => H.map c ≫ x) := by
  exact Generic.nativeHomFiveLemmaWithGroups (I := O.{u, v}) (B := B) E
    (omegaSourceHomGroups E hE)
    l m n r l' m' n' r' a b c d e z z'
    hl hm hn hl' hm' hn' hab hbc hcd hde hz ha hb hd he


end PointedCGWH.Spectra.Orthogonal.OriginalOmegaHoHomGroup
