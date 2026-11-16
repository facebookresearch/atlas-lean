/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.CameralNormalizerShifts

/-!
# Actual SL2 parameters for ramification compatibility

The parameter is retained before its image in G. The actual SL2 matrix
n(c) squares to minus identity; its image squares to the actual coroot
at minus one, which may be identity in PGL2. Conjugation transports c by
the inverse of the native adjoint coefficient on the chosen root vector.
Root and simple-reflection comparisons retain the canonical universal
frames and all Cartesian coefficient maps.
Source: Donagi--Gaitsgory arXiv:math/0005132v3, Sections 6.1--6.2 and 8.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CameralLiftedNormalizerModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj
open CameralFoundationPackages CameralRootSL2Sources CameralRamificationReindexing
open CameralRamificationTensorModels CameralRamificationTorsorReindexing
open CameralRamificationCocycles CameralCharacterRealizations CameralSimpleRootTrivializations
open CameralNormalizerShifts ContractedTorsorModels ExpansionParameterModels TorusLineFrameModels
open RankTwoMatrixGroupModels

theorem normalizerMatrix_square {A : Type} [CommRing A] (c : Aˣ) :
    normalizerMatrix c * normalizerMatrix c = diagonalMatrix (-1 : Aˣ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [normalizerMatrix, diagonalMatrix, weylMatrix, Matrix.mul_apply, Fin.sum_univ_two]

variable {G : Over (Spec (.of ℂ))} [GrpObj G] {tori : ∀ n : ℕ, TorusTheory ℂ n}
  (F : Foundation G tori) [GeneralLinearFrameSchemes.FrameTheory 2]
  [GL2MatrixTheory] [SL2MatrixTheory] (K : RootNormalizerGeometry G tori F)
  (D : RootTorsorInputs F K) (R : CanonicalRamificationFamily F K D)

attribute [local instance] CameralRamificationTensorModels.torusGroup

def minusOne (U : Over (Spec (.of ℂ))) : U ⟶ torusScheme ℂ 1 :=
  ((tori 1).units U).symm (fun _ => -1)

def transportedParameter (U : Over (Spec (.of ℂ))) (n : U ⟶ F.normalizer.scheme) (w : F.Weyl)
    (hn : Label F n w) (i j : Fin F.roots.count) (hij : K.permutations.index w i = j)
    (c : U ⟶ torusScheme ℂ 1) : U ⟶ torusScheme ℂ 1 := by
  letI := (tori 1).group
  exact CartesianMonoidalCategory.lift c
    ((K.transporters U n w hn i j hij).scalar ≫ ι[torusScheme ℂ 1]) ≫ μ[torusScheme ℂ 1]

structure TransportedNormalizerLift (U : Over (Spec (.of ℂ))) (n : U ⟶ F.normalizer.scheme)
    (w : F.Weyl) (hn : Label F n w) (i j : Fin F.roots.count)
    (hij : K.permutations.index w i = j) (c : U ⟶ torusScheme ℂ 1) where
  sl2 : CartesianMonoidalCategory.lift (𝟙 U) (c ≫ normalizerLift (tori 1)) ≫
      (K.transporters U n w hn i j hij).lift =
    transportedParameter F K U n w hn i j hij c ≫ normalizerLift (tori 1)
  group : SchemeLieJetFamilies.conjugate G (n ≫ F.normalizer.inclusion ≫ ι[G])
      (c ≫ (K.sl2 j).normalizer ≫ F.normalizer.inclusion) =
    transportedParameter F K U n w hn i j hij c ≫ (K.sl2 i).normalizer ≫ F.normalizer.inclusion

structure RootWeylGeometry where
  arrow : ∀ {X : Over (Spec (.of ℂ))} (C : Cover F X) (_w : F.Weyl), CameralArrow F C C
  total : ∀ {X : Over (Spec (.of ℂ))} (C : Cover F X) (w : F.Weyl),
    (arrow C w).total = (coverIso F C w).hom
  base : ∀ {X : Over (Spec (.of ℂ))} (C : Cover F X) (w : F.Weyl), (arrow C w).base = 𝟙 X
  reflection : ∀ {X : Over (Spec (.of ℂ))} (C : Cover F X) (w : F.Weyl)
      (i j : Fin F.roots.count) (_hij : K.permutations.index w i = j),
    ReflectionCompatible F (arrow C w) i j

def fixedTransport {X : Over (Spec (.of ℂ))} (C : Cover F X) (w : F.Weyl)
    (i j : Fin F.roots.count)
    (h : (reflection F C i).hom ≫ (coverIso F C w).hom.left =
      (coverIso F C w).hom.left ≫ (reflection F C j).hom) :
    fixedScheme F C i ⟶ fixedScheme F C j := by
  let f := equalizer.ι (reflection F C i).hom (𝟙 (total F C).left) ≫ (coverIso F C w).hom.left
  have hf : f ≫ (reflection F C j).hom = f ≫ 𝟙 (total F C).left := by
    dsimp only [f]
    rw [Category.assoc, ← h, ← Category.assoc, equalizer.condition]
    simp
  refine Over.homMk (equalizer.lift f hf) ?_
  change equalizer.lift f hf ≫
    (equalizer.ι (reflection F C j).hom (𝟙 (total F C).left) ≫ (total F C).hom) = _
  rw [← Category.assoc, equalizer.lift_ι]
  dsimp only [f, fixedScheme, Over.mk_hom]
  rw [Category.assoc, (coverIso F C w).hom.w]

omit [GeneralLinearFrameSchemes.FrameTheory 2] [GL2MatrixTheory] [SL2MatrixTheory] in
theorem fixedTransport_inclusion {X : Over (Spec (.of ℂ))} (C : Cover F X) (w : F.Weyl)
    (i j : Fin F.roots.count)
    (h : (reflection F C i).hom ≫ (coverIso F C w).hom.left =
      (coverIso F C w).hom.left ≫ (reflection F C j).hom) :
    fixedTransport F C w i j h ≫ fixedInclusion F C j =
      fixedInclusion F C i ≫ (coverIso F C w).hom := by
  apply Over.OverMorphism.ext
  dsimp only [fixedTransport, fixedInclusion, Over.homMk_left, Over.comp_left]
  exact equalizer.lift_ι _ _

structure SimpleReflectionTorsors where
  iso : ∀ {X : Over (Spec (.of ℂ))} (C : Cover F X) (i : Fin F.roots.count)
      (_hi : SimpleRoot G tori F i),
    ramificationTorsor F K D C (F.roots.reflection i) ≅ rootTorsor F K D C i
  universal : ∀ (i : Fin F.roots.count) (hi : SimpleRoot G tori F i),
    (universalRamificationPoint F K D R.universal R.rootFrames (F.roots.reflection i)).val ≫
      (iso R.universal.cover i hi).hom.iso.hom =
    (universalRootPoint F K D R.universal R.rootFrames i).val
  base_change : ∀ {X X' : Over (Spec (.of ℂ))} {C : Cover F X} {C' : Cover F X'}
      (m : CameralArrow F C C') (h : ∀ j, ReflectionCompatible F m j j)
      (i : Fin F.roots.count) (hi : SimpleRoot G tori F i),
    (D.torus.baseChange.change m.total).map (iso C' i hi).hom ≫
      (R.torsors.roots m i (h i)).root.hom =
    (ramificationPullbackIso F K D R.symbols R.torsors m h (F.roots.reflection i)).hom ≫
      (iso C i hi).hom

end MathlibExt.AlgebraicGeometry.CameralLiftedNormalizerModels
