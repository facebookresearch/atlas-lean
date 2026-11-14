/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import MathlibExt.AlgebraicGeometry.CurvePositivity
public import MathlibExt.AlgebraicGeometry.CurveCohomologyCalculus
public import MathlibExt.AlgebraicGeometry.FiniteCoverLocalComparison
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public noncomputable section

/-!
# The actual split algebra of a smooth spectral cover

The numerical BNR formulas only need the finite flat cover and the
underlying module decomposition of its algebra into negative powers of
the twisting line bundle. The model supplies those geometric data, and
contains no genus, pushforward-rank or degree conclusion. It applies to
the smooth integral spectral-curve slice; it does not assert the whole
Higgs/spectral correspondence or nonabelian Hodge theory.

The conditional integration results below have completed proofs. Their
inputs expose the existing generic curve tensor/Euler calculus, the
actual pushed injective-resolution unit, canonical open-base-change
mates and ordinary line trivializations. No BNR numerical conclusion is
an input. These are ports and assembly of covered mathematics, rather
than unresolved requests for those numerical formulas.

Source: Beauville--Narasimhan--Ramanan, *Spectral curves and the
generalised theta divisor*, §3, especially Remark 3.2 and Proposition 3.6.
https://math.univ-cotedazur.fr/u/beauvill/pubs/bnr.pdf
-/

namespace MathlibExt.AlgebraicGeometry.SpectralCurveNumerics

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open _root_.MathlibExt.AlgebraicGeometry.CurveVectorBundles
open _root_.MathlibExt.AlgebraicGeometry.CurvePositivity
open _root_.MathlibExt.AlgebraicGeometry.CurveCohomologyCalculus
open _root_.MathlibExt.AlgebraicGeometry.FiniteCoverLocalComparison

universe u

/-- Actual cover with the standard spectral algebra splitting as an
explicit geometric input. The morphism in `Over` includes the
base-field compatibility equation. -/
structure SplitSpectralCover {k : Type u} [Field k]
    (C : Over (Spec (.of k))) (L : C.left.Modules) (n : ℕ) where
  line : IsLineBundle L
  inverseLine : C.left.Modules
  inverseIsLine : IsLineBundle inverseLine
  inverseTensor : Nonempty
    (moduleTensor C.left L inverseLine ≅ structureModule C.left)
  S : Over (Spec (.of k))
  [proper : IsProper S.hom]
  [smoothCurve : SmoothOfRelativeDimension 1 S.hom]
  [irreducible : GeometricallyIrreducible S.hom]
  q : S ⟶ C
  [finite : IsFinite q.left]
  [flat : Flat q.left]
  algebraSplitting : Nonempty
    ((Scheme.Modules.pushforward q.left).obj (structureModule S.left) ≅
      ∐ fun i : Fin n ↦ power inverseLine i.val)

/-- The spectral transform uses the actual finite direct-image functor. -/
abbrev spectralPushforward {k : Type u} [Field k]
    {C : Over (Spec (.of k))} {L : C.left.Modules} {n : ℕ}
    (P : SplitSpectralCover C L n) (M : P.S.left.Modules) : C.left.Modules :=
  (Scheme.Modules.pushforward P.q.left).obj M

variable {k : Type u} [Field k] {C : Over (Spec (.of k))}
  {L : C.left.Modules} {n : ℕ}

/-- Source-covered geometric toolkit data on the actual current carriers.
The mapped unit is fixed by the chosen injective resolution. Neither
spectral genus, rank nor degree is assumed by any field. -/
structure SpectralCohomologyInputs (P : SplitSpectralCover C L n) where
  tensor : CurveTensorEulerInputs C.hom
  constantsBase : HasFieldGlobalSections C.hom
  constantsCover : HasFieldGlobalSections P.S.hom
  structureResolution : MappedResolutionConditions (Scheme.Modules.pushforward P.q.left)
    (injectiveResolution (structureModule P.S.left))

/-- Ordinary source-covered input for a spectral line: actual acyclicity
of the pushed resolution and rank-one trivializations on actual finite
preimage opens. No pushforward rank/degree conclusion is a field. -/
structure SpectralLineInputs (P : SplitSpectralCover C L n) (M : P.S.left.Modules) where
  line : IsLineBundle M
  resolution : MappedResolutionConditions (Scheme.Modules.pushforward P.q.left)
    (injectiveResolution M)
  charts : ∀ x : C.left,
    FiniteLineChart P.q.left (fun i : Fin n ↦ power P.inverseLine i.val) M x

theorem inverse_degree (P : SplitSpectralCover C L n) (I : SpectralCohomologyInputs P) :
    degree C.hom P.inverseLine = -degree C.hom L := by
  have hT := tensor_degree C.hom I.tensor L P.inverseLine P.line P.inverseIsLine
  have hI := degree_eq_of_iso C.hom P.inverseTensor.some
  rw [degree_structure] at hI
  linarith

/-- Euler characteristic of the spectral structure sheaf, proved by the
canonical cohomology comparison, the actual split algebra and the generic
covered tensor-degree law. -/
theorem spectralStructureEuler (P : SplitSpectralCover C L n)
    (I : SpectralCohomologyInputs P) :
    euler01 P.S.hom (structureModule P.S.left) =
      (n : ℤ) * euler01 C.hom (structureModule C.left) -
        (∑ i : Fin n, (i.val : ℤ)) * degree C.hom L := by
  have hp := euler01_pushforward P.q.left C.hom (structureModule P.S.left) I.structureResolution
  rw [P.q.w] at hp
  let A : Fin n → C.left.Modules := fun i ↦ power P.inverseLine i.val
  have hA : ∀ i, IsLineBundle (A i) := fun i ↦
    power_isLine C.hom I.tensor P.inverseLine P.inverseIsLine i.val
  calc
    euler01 P.S.hom (structureModule P.S.left) =
        euler01 C.hom ((Scheme.Modules.pushforward P.q.left).obj
          (structureModule P.S.left)) := hp.symm
    _ = euler01 C.hom (∐ A) := euler01_eq_of_iso C.hom P.algebraSplitting.some
    _ = ∑ i, euler01 C.hom (A i) :=
      euler01_coproduct C.hom A
        (fun i ↦ I.tensor.finite (A i) (hA i) 0 (by omega))
        (fun i ↦ I.tensor.finite (A i) (hA i) 1 (by omega))
    _ = ∑ i : Fin n, (euler01 C.hom (structureModule C.left) - i.val * degree C.hom L) := by
      apply Finset.sum_congr rfl
      intro i hi
      have hpow := degree_power C.hom I.tensor P.inverseLine P.inverseIsLine i.val
      rw [inverse_degree P I] at hpow
      have he := degree_eq_euler01_sub C.hom (A i)
      change degree C.hom (A i) = (i.val : ℤ) * -degree C.hom L at hpow
      linarith
    _ = _ := by
      simp only [Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem twice_sum_fin_indices (n : ℕ) :
    2 * (∑ i : Fin n, (i.val : ℤ)) = (n : ℤ) * ((n : ℤ) - 1) := by
  induction n with
  | zero => simp
  | succ n hn =>
      rw [Fin.sum_univ_castSucc]
      simp only [Fin.val_castSucc, Fin.val_last]
      push_cast
      nlinarith

/-- The BNR spectral genus formula as a completed integration result.
Its hypotheses expose covered primitive comparisons on actual objects;
they do not assume this genus equation. -/
theorem spectralGenus [IsAlgClosed k] [CharZero k] [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    (P : SplitSpectralCover C L n) (_hn : 0 < n)
    (I : SpectralCohomologyInputs P) :
    2 * ((genus P.S.hom : ℤ) - 1) =
      2 * (n : ℤ) * ((genus C.hom : ℤ) - 1) +
        (n : ℤ) * ((n : ℤ) - 1) * degree C.hom L := by
  have := I.constantsBase
  have := I.constantsCover
  have he := spectralStructureEuler P I
  rw [euler01_structure C.hom, euler01_structure P.S.hom] at he
  have hs := congrArg (fun z : ℤ ↦ z * degree C.hom L) (twice_sum_fin_indices n)
  nlinarith

/-- Rank n is assembled from actual finite-open line trivializations and
the actual algebra splitting, with no rank-n statement supplied as input. -/
theorem spectralPushforwardRank (P : SplitSpectralCover C L n) (M : P.S.left.Modules)
    (J : SpectralLineInputs P M) : IsVectorBundle (spectralPushforward P M) n :=
  pushforward_rank_from_charts P.q.left (fun i : Fin n ↦ power P.inverseLine i.val) M
    P.algebraSplitting.some J.charts

/-- The precise BNR degree shift, proved on the existing Euler-characteristic
degree carrier through the canonical affine cohomology comparison. -/
theorem spectralPushforwardDegree (P : SplitSpectralCover C L n)
    (I : SpectralCohomologyInputs P) (M : P.S.left.Modules) (J : SpectralLineInputs P M) :
    2 * bundleDegree C.hom (spectralPushforward P M) n =
      2 * degree P.S.hom M - (n : ℤ) * ((n : ℤ) - 1) * degree C.hom L := by
  have hm := euler01_pushforward P.q.left C.hom M J.resolution
  rw [P.q.w] at hm
  have ho := spectralStructureEuler P I
  have hd := degree_eq_euler01_sub P.S.hom M
  rw [bundleDegree_eq_euler01_sub]
  change euler01 C.hom (spectralPushforward P M) = euler01 P.S.hom M at hm
  have hs := congrArg (fun z : ℤ ↦ z * degree C.hom L) (twice_sum_fin_indices n)
  nlinarith

theorem spectralPushforwardRankDegree [IsAlgClosed k] [CharZero k] [IsProper C.hom]
    [SmoothOfRelativeDimension 1 C.hom] [GeometricallyIrreducible C.hom]
    (P : SplitSpectralCover C L n) (_hn : 0 < n)
    (I : SpectralCohomologyInputs P) (M : P.S.left.Modules) (J : SpectralLineInputs P M) :
    IsVectorBundle (spectralPushforward P M) n ∧
      2 * bundleDegree C.hom (spectralPushforward P M) n =
        2 * degree P.S.hom M - (n : ℤ) * ((n : ℤ) - 1) * degree C.hom L :=
  ⟨spectralPushforwardRank P M J, spectralPushforwardDegree P I M J⟩

end MathlibExt.AlgebraicGeometry.SpectralCurveNumerics

