/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DeligneSymbolModels

/-!
# Source-normalized cubical extension of Deligne symbols

The determinant functor in relative dimension n has its canonical
(n+2)-cubical trivialization. Its regular normalization is the image of
the actual full section Koszul torsion, with the SAME affine subset
presentations. Its symmetric cocycle law is tested using literal common
subset presentations and shared exterior bases, not fresh comparisons.
This cubical structure supplies the tensor quotient extension needed for
rational sections of arbitrary line bundles, including negative lines.

Sources: Yuan--Zhang, arXiv:2105.13587v9, Section 4.2.1, pp108--110;
Knudsen--Mumford, Sections 1--2; Ducrot, *Cube structures and intersection
bundles*, the determinant cubical structure and multilinear extension.
Construction and uniqueness remain direct Wanted requests.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DeligneCubicalModels

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry
open CoherentCurveLinearSeries RelativeDeterminantPairings
open GlobalBoundedDeterminantModels BoundedProjectiveDeterminants
open DeligneSymbolModels CanonicalKoszulDeterminants
open scoped TensorProduct

attribute [local instance] HasDerivedCategory.standard

variable [FourierMukai.HasDerivedPullbacks.{0}] [FourierMukai.HasDerivedPushforwards.{0}]
  [AffineDerivedCoefficientModules.HasDerivedScalarExtensions.{0}]
  [∀ R : CommRingCat.{0}, PreservesFiniteLimits (tilde.functor R)]
  [∀ R : CommRingCat.{0}, BoundedProjectiveDeterminants.ProjectiveSources R]

/-- Same-source affine transport uses exactly the two ORIGINAL comparisons. -/
def factorSamePresentation {X Y : Scheme.{0}} {f : X ⟶ Y} {m : ℕ}
    {L : Fin m → X.Modules} {R : CommRingCat.{0}} {a : Spec R ⟶ Y}
    (I : DeterminantSources) (P Q : Presentations f L R a)
    (F : (AffineDerivedCoefficientModules.derivedTilde R).FullyFaithful)
    (t : Finset (Fin m)) : factor P t ≅ factor Q t := by
  classical
  let e := (I.transport R).map ⟨(P t).complex⟩ ⟨(Q t).complex⟩
    (F.preimageIso ((P t).comparison ≪≫ (Q t).comparison.symm))
  by_cases h : IsPositive t
  · simpa only [factor, h, ite_true] using e
  · simpa only [factor, h, ite_false] using e.toLinearEquiv.symm.dualMap.toModuleIso

def pairingSamePresentationFold {X Y : Scheme.{0}} {f : X ⟶ Y} {m : ℕ}
    {L : Fin m → X.Modules} {R : CommRingCat.{0}} {a : Spec R ⟶ Y}
    (I : DeterminantSources) (P Q : Presentations f L R a)
    (F : (AffineDerivedCoefficientModules.derivedTilde R).FullyFaithful) :
    (ss : List (Finset (Fin m))) →
      GlobalBoundedDeterminantModels.pairingFold P ss ≅ GlobalBoundedDeterminantModels.pairingFold Q ss
  | [] => Iso.refl _
  | t :: ss => tensorIso (factorSamePresentation I P Q F t) (pairingSamePresentationFold I P Q F ss)

def pairingSamePresentation {X Y : Scheme.{0}} {f : X ⟶ Y} {m : ℕ}
    {L : Fin m → X.Modules} {R : CommRingCat.{0}} {a : Spec R ⟶ Y}
    (I : DeterminantSources) (P Q : Presentations f L R a)
    (F : (AffineDerivedCoefficientModules.derivedTilde R).FullyFaithful) :
    localPairing P ≅ localPairing Q :=
  pairingSamePresentationFold I P Q F (subsets m)

def unionBlocks {d k : ℕ} (b : Fin k → Finset (Fin d)) (t : Finset (Fin k)) : Finset (Fin d) :=
  t.biUnion b

def groupedLines {X : Scheme.{0}} {d k : ℕ} (L : Fin d → X.Modules)
    (b : Fin k → Finset (Fin d)) : Fin k → X.Modules := fun i ↦ subsetTensor L (b i)

/-- Canonical tensor regrouping is fixed on EVERY actual local pure section. -/
structure GroupingSources {X : Scheme.{0}} {d k : ℕ} (L : Fin d → X.Modules)
    (b : Fin k → Finset (Fin d)) where
  disjoint : Pairwise (fun i j ↦ Disjoint (b i) (b j))
  subsetIso : ∀ t : Finset (Fin k),
    subsetTensor L (unionBlocks b t) ≅ subsetTensor (groupedLines L b) t
  normalized : ∀ (t : Finset (Fin k)) (U : X.Opens) (e : ∀ i : Fin d, Γ(L i,U)),
    (subsetIso t).hom.app U (subsetSection L U e (unionBlocks b t)) =
      subsetSection (groupedLines L b) U (fun i ↦ subsetSection L U e (b i)) t

def groupedPresentations {X Y : Scheme.{0}} {f : X ⟶ Y} {d k : ℕ}
    {L : Fin d → X.Modules} {b : Fin k → Finset (Fin d)}
    {R : CommRingCat.{0}} {a : Spec R ⟶ Y}
    (P : Presentations f L R a) (G : GroupingSources L b) :
    Presentations f (groupedLines L b) R a := fun t ↦
  ⟨(P (unionBlocks b t)).complex, (P (unionBlocks b t)).comparison ≪≫
    (FourierMukai.derivedPullback a).mapIso
      ((FourierMukai.derivedPushforward f).mapIso
        ((DerivedCategory.singleFunctor X.Modules 0).mapIso (G.subsetIso t)))⟩

def groupedBases {X Y : Scheme.{0}} {f : X ⟶ Y} {d k : ℕ}
    {L : Fin d → X.Modules} {b : Fin k → Finset (Fin d)}
    {R : CommRingCat.{0}} {a : Spec R ⟶ Y}
    (P : Presentations f L R a) (G : GroupingSources L b)
    (B : FreeSubsetBases R (fun t ↦ (P t).complex)) :
    FreeSubsetBases R (fun t ↦ (groupedPresentations P G t).complex) :=
  fun t ↦ B (unionBlocks b t)

/-- The four actual faces of the symmetric tensor cocycle (AB,C), (A,B), (A,BC), (B,C). -/
def cocycleBlocks (n : ℕ) (face : Fin 4) (i : Fin (n+2)) : Finset (Fin (n+3)) := by
  classical
  let a : Fin (n+3) := ⟨0, by omega⟩
  let b : Fin (n+3) := ⟨1, by omega⟩
  let c : Fin (n+3) := ⟨2, by omega⟩
  exact if i.val = 0 then
    if face.val = 0 then {a,b} else if face.val = 3 then {b} else {a}
    else if i.val = 1 then
      if face.val = 1 then {b} else if face.val = 2 then {b,c} else {c}
    else {⟨i.val+1, by omega⟩}

def permutationBlocks {m : ℕ} (σ : Equiv.Perm (Fin m)) (i : Fin m) : Finset (Fin m) :=
  {σ i}

/-- The genuine structure-module unit in one slot, with actual zero sections elsewhere. -/
def unitSections {Z : Scheme.{0}} {m : ℕ} (L : Fin m → Z.Modules) (j : Fin m)
    (h : L j = structureModule Z) : ∀ i : Fin m, Γ(L i,⊤) := by
  intro i
  by_cases hi : i = j
  · subst i
    rw [h]
    change Γ(Z,⊤)
    exact 1
  · exact 0

variable {X Y : Scheme.{0}} (I : DeterminantSources) (f : X ⟶ Y) (n : ℕ)

/-- Canonical determinant cubical data on actual scheme line bundles.
The cocycle/symmetry laws use shared cochains and shared exterior coordinates;
regular normalization uses actual acyclic torsion. There is no symbol word. -/
structure CubicalSources where
  projective : ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ Y),
    RelativePolynomialProjectivity.IsProjective (pullback.snd f a)
  finiteTor : FiniteTorDimension f
  pureDimension : IsPureRelativeDimension f n
  cube : ∀ (L : Fin (n+2) → X.Modules), (∀ i, IsLineBundle (L i)) →
    ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ Y) (P : Presentations f L R a),
      localPairing P ≅ 𝟙_ (ModuleCat.{0} R)
  regular : ∀ (L : Fin (n+2) → X.Modules) (hL : ∀ i, IsLineBundle (L i))
    (s : ∀ i, Γ(L i,⊤)) (K : FullSectionKoszul L s)
    (R : CommRingCat.{0}) (a : Spec R ⟶ Y) (P : Presentations f L R a)
    (C : FullKoszulAffineSource f L s K R a P)
    (E : CanonicalEvaluation I (fun t ↦ (P t).complex) C.complex C.toTotalTermModel.assembly),
      (cube L hL R a P).hom E.value = (1 : R)
  samePresentation : ∀ (L : Fin (n+2) → X.Modules) (hL : ∀ i, IsLineBundle (L i))
    (R : CommRingCat.{0}) (a : Spec R ⟶ Y) (P Q : Presentations f L R a)
    (F : (AffineDerivedCoefficientModules.derivedTilde R).FullyFaithful),
      (pairingSamePresentation I P Q F).hom ≫ (cube L hL R a Q).hom = (cube L hL R a P).hom
  scalar : ∀ (L : Fin (n+2) → X.Modules) (hL : ∀ i, IsLineBundle (L i))
    {R S : CommRingCat.{0}} (g : R ⟶ S) (a : Spec R ⟶ Y) (a' : Spec S ⟶ Y)
    (h : Spec.map g ≫ a = a') (P : Presentations f L R a) (Q : Presentations f L S a')
    (C : DeterminantPullbackCoherence.Coherence.{0})
    (B : AffineDerivedCoefficientModules.DerivedComparison g)
    (F : (AffineDerivedCoefficientModules.derivedTilde S).FullyFaithful)
    (T : DeterminantScalarTensorModels.ScalarTensorSources g),
      (pairingTransition I f L g a a' h P Q C B F T).hom ≫ (cube L hL S a' Q).hom =
        (ModuleCat.extendScalars g.hom).map (cube L hL R a P).hom ≫ T.unit.hom
  cocycle : ∀ (L : Fin (n+3) → X.Modules)
    (G : ∀ face : Fin 4, GroupingSources L (cocycleBlocks n face))
    (hL : ∀ (face : Fin 4) (i : Fin (n+2)), IsLineBundle (groupedLines L (cocycleBlocks n face) i))
    (R : CommRingCat.{0}) (a : Spec R ⟶ Y) (P : Presentations f L R a)
    (B : FreeSubsetBases R (fun t ↦ (P t).complex)),
    let c := fun face : Fin 4 ↦
      (cube (groupedLines L (cocycleBlocks n face)) (hL face) R a
        (groupedPresentations P (G face))).hom
        (pairingVector R (fun t ↦ (groupedPresentations P (G face) t).complex)
          (groupedBases P (G face) B) (subsets (n+2)))
    c 0 * c 1 = c 2 * c 3
  symmetry : ∀ (L : Fin (n+2) → X.Modules) (hL : ∀ i, IsLineBundle (L i))
    (σ : Equiv.Perm (Fin (n+2))) (G : GroupingSources L (permutationBlocks σ))
    (hG : ∀ i, IsLineBundle (groupedLines L (permutationBlocks σ) i))
    (R : CommRingCat.{0}) (a : Spec R ⟶ Y) (P : Presentations f L R a)
    (B : FreeSubsetBases R (fun t ↦ (P t).complex)),
    (cube (groupedLines L (permutationBlocks σ)) hG R a (groupedPresentations P G)).hom
      (pairingVector R (fun t ↦ (groupedPresentations P G t).complex)
        (groupedBases P G B) (subsets (n+2))) =
      (cube L hL R a P).hom (pairingVector R (fun t ↦ (P t).complex) B (subsets (n+2)))

def splitCubeLines (N : Fin (n+1) → X.Modules) (B : X.Modules) : Fin (n+2) → X.Modules :=
  Fin.snoc N B

/-- Face0 is the original tuple, face1 its negative replacement, face2 its positive replacement. -/
def splitFaceLines (N : Fin (n+1) → X.Modules) (j : Fin (n+1)) (B A : X.Modules)
    (face : Fin 3) : Fin (n+1) → X.Modules :=
  if face.val = 0 then N else Function.update N j (if face.val = 1 then B else A)

def splitFaceSubset (j : Fin (n+1)) (face : Fin 3) (t : Finset (Fin (n+1))) :
    Finset (Fin (n+2)) := by
  classical
  let extra : Finset (Fin (n+2)) := if j ∈ t then {Fin.last (n+1)} else ∅
  exact if face.val = 0 then t.map Fin.castSuccEmb
    else if face.val = 1 then (t.erase j).map Fin.castSuccEmb ∪ extra
    else t.map Fin.castSuccEmb ∪ extra

def splitFaceSection (N : Fin (n+1) → X.Modules) (j : Fin (n+1)) (B A : X.Modules)
    (e : CurvePositivity.moduleTensor X (N j) B ≅ A) (face : Fin 3) (U : X.Opens)
    (s : ∀ i : Fin (n+2), Γ(splitCubeLines n N B i,U)) :
    ∀ i : Fin (n+1), Γ(splitFaceLines n N j B A face i,U) := by
  classical
  intro i
  by_cases hf : face.val = 0
  · simpa [splitFaceLines, hf, splitCubeLines] using s i.castSucc
  · by_cases hi : i = j
    · subst i
      by_cases hn : face.val = 1
      · simpa [splitFaceLines, hf, hn, splitCubeLines] using s (Fin.last (n+1))
      · have sj : Γ(N j,U) := by simpa [splitCubeLines] using s j.castSucc
        have sb : Γ(B,U) := by simpa [splitCubeLines] using s (Fin.last (n+1))
        simpa [splitFaceLines, hf, hn] using
          e.hom.app U (MetrizedFibrePowerModels.tensorSectionAt (N j) B U sj sb)
    · simpa [splitFaceLines, hf, hi, splitCubeLines] using s i.castSucc

/-- Every endpoint subset comparison is fixed by the actual tensor fraction
isomorphism and the original local sections, including the scalar units. -/
structure TensorOriginSources (N : Fin (n+1) → X.Modules) (j : Fin (n+1)) (B A : X.Modules)
    (e : CurvePositivity.moduleTensor X (N j) B ≅ A) where
  subsetIso : ∀ (face : Fin 3) (t : Finset (Fin (n+1))),
    subsetTensor (splitCubeLines n N B) (splitFaceSubset n j face t) ≅
      subsetTensor (splitFaceLines n N j B A face) t
  normalized : ∀ (face : Fin 3) (t : Finset (Fin (n+1))) (U : X.Opens)
    (s : ∀ i : Fin (n+2), Γ(splitCubeLines n N B i,U)),
    (subsetIso face t).hom.app U
      (subsetSection (splitCubeLines n N B) U s (splitFaceSubset n j face t)) =
        subsetSection (splitFaceLines n N j B A face) U (splitFaceSection n N j B A e face U s) t

def tensorSharedPresentations {N : Fin (n+1) → X.Modules} {j : Fin (n+1)} {B A : X.Modules}
    {e : CurvePositivity.moduleTensor X (N j) B ≅ A} {R : CommRingCat.{0}} {a : Spec R ⟶ Y}
    (P : Presentations f (splitCubeLines n N B) R a) (S : TensorOriginSources n N j B A e)
    (face : Fin 3) : Presentations f (splitFaceLines n N j B A face) R a := fun t ↦
  ⟨(P (splitFaceSubset n j face t)).complex, (P (splitFaceSubset n j face t)).comparison ≪≫
    (FourierMukai.derivedPullback a).mapIso
      ((FourierMukai.derivedPushforward f).mapIso
        ((DerivedCategory.singleFunctor X.Modules 0).mapIso (S.subsetIso face t)))⟩

def tensorSharedBases {N : Fin (n+1) → X.Modules} {j : Fin (n+1)} {B A : X.Modules}
    {e : CurvePositivity.moduleTensor X (N j) B ≅ A} {R : CommRingCat.{0}} {a : Spec R ⟶ Y}
    (P : Presentations f (splitCubeLines n N B) R a) (S : TensorOriginSources n N j B A e)
    (V : FreeSubsetBases R (fun t ↦ (P t).complex)) (face : Fin 3) :
    FreeSubsetBases R (fun t ↦ (tensorSharedPresentations f n P S face t).complex) :=
  fun t ↦ V (splitFaceSubset n j face t)

structure TensorFreeCover (N : Fin (n+1) → X.Modules) (j : Fin (n+1)) (B A : X.Modules)
    (e : CurvePositivity.moduleTensor X (N j) B ≅ A) (R : CommRingCat.{0}) (a : Spec R ⟶ Y) where
  index : Type
  ring : index → CommRingCat.{0}
  element : index → R
  map : ∀ c : index, R ⟶ ring c
  [algebra : ∀ c : index, Algebra R (ring c)]
  map_normalized : ∀ c : index, (map c).hom = algebraMap R (ring c)
  [localization : ∀ c : index, IsLocalization.Away (element c) (ring c)]
  [openMap : ∀ c : index, IsOpenImmersion (Spec.map (map c))]
  cover : ∀ x : Spec R, ∃ (c : index) (y : Spec (ring c)), Spec.map (map c) y = x
  source : TensorOriginSources n N j B A e
  presentation : ∀ c : index,
    Presentations f (splitCubeLines n N B) (ring c) (Spec.map (map c) ≫ a)
  bases : ∀ c : index, FreeSubsetBases (ring c) (fun t ↦ (presentation c t).complex)
  faithful : ∀ c : index, (AffineDerivedCoefficientModules.derivedTilde (ring c)).FullyFaithful

/-- The tensor comparator is fixed by the SAME common (n+2)-cube coefficient,
actual fraction tensor map, shared subset cochains and all exterior bases.
Principal covers make this formula nonvacuous even for negative/nonfree lines. -/
structure TensorComparisonSources (C : CubicalSources I f n)
    (N : Fin (n+1) → X.Modules) (j : Fin (n+1)) (B A : X.Modules)
    (e : CurvePositivity.moduleTensor X (N j) B ≅ A) where
  cubeLine : ∀ i : Fin (n+2), IsLineBundle (splitCubeLines n N B i)
  freeCover : ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ Y), TensorFreeCover f n N j B A e R a
  comparison : ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ Y)
    (P : ∀ face : Fin 3, Presentations f (splitFaceLines n N j B A face) R a),
      (localPairing (P 0) ⊗ localPairing (P 1)) ≅ localPairing (P 2)
  normalized : ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ Y)
    (P : ∀ face : Fin 3, Presentations f (splitFaceLines n N j B A face) R a)
    (Q : Presentations f (splitCubeLines n N B) R a) (S : TensorOriginSources n N j B A e)
    (F : (AffineDerivedCoefficientModules.derivedTilde R).FullyFaithful)
    (V : FreeSubsetBases R (fun t ↦ (Q t).complex)),
    let v := fun face : Fin 3 ↦
      (pairingSamePresentation I (tensorSharedPresentations f n Q S face) (P face) F).hom
        (pairingVector R (fun t ↦ (tensorSharedPresentations f n Q S face t).complex)
          (tensorSharedBases f n Q S V face) (subsets (n+1)))
    (C.cube (splitCubeLines n N B) cubeLine R a Q).hom
      (pairingVector R (fun t ↦ (Q t).complex) V (subsets (n+2))) •
        (comparison R a P).hom (v 0 ⊗ₜ[R] v 1) = v 2
  scalar : ∀ {R S : CommRingCat.{0}} (g : R ⟶ S)
    (a : Spec R ⟶ Y) (a' : Spec S ⟶ Y) (h : Spec.map g ≫ a = a')
    (P : ∀ face : Fin 3, Presentations f (splitFaceLines n N j B A face) R a)
    (Q : ∀ face : Fin 3, Presentations f (splitFaceLines n N j B A face) S a')
    (H : DeterminantPullbackCoherence.Coherence.{0})
    (D : AffineDerivedCoefficientModules.DerivedComparison g)
    (F : (AffineDerivedCoefficientModules.derivedTilde S).FullyFaithful)
    (T : DeterminantScalarTensorModels.ScalarTensorSources g),
    (T.tensor (localPairing (P 0)) (localPairing (P 1))).hom ≫
      (tensorIso
        (pairingTransition I f (splitFaceLines n N j B A 0) g a a' h (P 0) (Q 0) H D F T)
        (pairingTransition I f (splitFaceLines n N j B A 1) g a a' h (P 1) (Q 1) H D F T)).hom ≫
        (comparison S a' Q).hom =
      (ModuleCat.extendScalars g.hom).map (comparison R a P).hom ≫
        (pairingTransition I f (splitFaceLines n N j B A 2) g a a' h (P 2) (Q 2) H D F T).hom

def fractionBranchLines {N : Fin (n+1) → X.Modules}
    {q : ∀ i : Fin (n+1), RationalSection (N i)}
    (F : ∀ i : Fin (n+1), CartierFraction (N i) (q i))
    (b : Fin (n+1) → Bool) : Fin (n+1) → X.Modules :=
  fun i ↦ if b i then (F i).negativeLine else (F i).positiveLine

/-- Actual fraction sources whose EVERY signed regular branch is retained. -/
structure FractionRegularTuple (N : Fin (n+1) → X.Modules)
    (q : ∀ i : Fin (n+1), RationalSection (N i)) where
  fraction : ∀ i : Fin (n+1), CartierFraction (N i) (q i)
  branch : ∀ b : Fin (n+1) → Bool, RegularTuple f n (fractionBranchLines n fraction b)
  positiveSource : ∀ (b : Fin (n+1) → Bool) (i : Fin (n+1)), b i = false →
    HEq ((branch b).sectionValue i) (fraction i).numerator
  negativeSource : ∀ (b : Fin (n+1) → Bool) (i : Fin (n+1)), b i = true →
    HEq ((branch b).sectionValue i) (fraction i).denominator

/-- Rational symbol derivations use canonical regular Koszul torsions and
canonical tensor quotient maps. Every recursive factor retains its actual
rational section/fraction; no new determinant word or rescaling is admitted. -/
inductive RationalExpression (C : CubicalSources I f n) :
    (N : Fin (n+1) → X.Modules) → (∀ i : Fin (n+1), RationalSection (N i)) →
    (P : ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ Y), Presentations f N R a) →
    (∀ (R : CommRingCat.{0}) (a : Spec R ⟶ Y), Module.Basis Unit R (localPairing (P R a))) → Type 1
  | regular {N : Fin (n+1) → X.Modules} {q : ∀ i : Fin (n+1), RationalSection (N i)}
      (P : ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ Y), Presentations f N R a)
      (D : DeligneLine I f n N P) (s : RegularTuple f n N) (S : SymbolSources I f n N P D s)
      (source : ∀ i : Fin (n+1), (q i).value =
        (N i).val.map (homOfLE (le_top : (q i).domain ≤ ⊤)).op (s.sectionValue i))
      (B : ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ Y), Module.Basis Unit R (localPairing (P R a)))
      (normalized : ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ Y), B R a () = localSymbol I f n N P D s S R a) :
      RationalExpression C N q P B
  | fraction {N : Fin (n+1) → X.Modules} {q : ∀ i : Fin (n+1), RationalSection (N i)}
      (j : Fin (n+1)) (F : CartierFraction (N j) (q j))
      (qPositive : ∀ i : Fin (n+1), RationalSection (splitFaceLines n N j F.negativeLine F.positiveLine 2 i))
      (qNegative : ∀ i : Fin (n+1), RationalSection (splitFaceLines n N j F.negativeLine F.positiveLine 1 i))
      (positiveSource : HEq (qPositive j).value
        (F.positiveLine.val.map (homOfLE (le_top : (qPositive j).domain ≤ ⊤)).op F.numerator))
      (negativeSource : HEq (qNegative j).value
        (F.negativeLine.val.map (homOfLE (le_top : (qNegative j).domain ≤ ⊤)).op F.denominator))
      (otherPositive : ∀ i : Fin (n+1), i ≠ j → HEq (qPositive i) (q i))
      (otherNegative : ∀ i : Fin (n+1), i ≠ j → HEq (qNegative i) (q i))
      (T : TensorComparisonSources I f n C N j F.negativeLine F.positiveLine F.comparison)
      (P : ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ Y) (face : Fin 3),
        Presentations f (splitFaceLines n N j F.negativeLine F.positiveLine face) R a)
      (B : ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ Y) (face : Fin 3),
        Module.Basis Unit R (localPairing (P R a face)))
      (positive : RationalExpression C (splitFaceLines n N j F.negativeLine F.positiveLine 2)
        qPositive (fun R a ↦ P R a 2) (fun R a ↦ B R a 2))
      (negative : RationalExpression C (splitFaceLines n N j F.negativeLine F.positiveLine 1)
        qNegative (fun R a ↦ P R a 1) (fun R a ↦ B R a 1))
      (normalized : ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ Y),
        (T.comparison R a (P R a)).hom (B R a 0 () ⊗ₜ[R] B R a 1 ()) = B R a 2 ()) :
      RationalExpression C N q (fun R a ↦ P R a 0) (fun R a ↦ B R a 0)

variable {I f n} in
/-- The local generator carries the canonical torsion/quotient derivation above. -/
def RationalExpression.value {C : CubicalSources I f n}
    {N : Fin (n+1) → X.Modules} {q : ∀ i : Fin (n+1), RationalSection (N i)}
    {P : ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ Y), Presentations f N R a}
    {B : ∀ (R : CommRingCat.{0}) (a : Spec R ⟶ Y), Module.Basis Unit R (localPairing (P R a))}
    (_E : RationalExpression I f n C N q P B) (R : CommRingCat.{0}) (a : Spec R ⟶ Y) :
    localPairing (P R a) := B R a ()

end MathlibExt.AlgebraicGeometry.DeligneCubicalModels
