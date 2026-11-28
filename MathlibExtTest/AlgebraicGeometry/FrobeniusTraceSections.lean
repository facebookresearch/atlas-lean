/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.FrobeniusTraceSections
import MathlibExt.AlgebraicGeometry.FrobeniusCenterDifferent

/-!
# Tests for Frobenius trace sections and the F-different

`S0` lies in the trace image of every admissible exponent; the local test infimum lies in every
nonzero ideal compatible with all local traces, and is the least one when nonzero; and
`(p^e - 1)` times the F-different is `D₀ - D_N + div(r)`.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.FourierMukai
open MathlibExt.AlgebraicGeometry.FrobeniusGeometry
open MathlibExt.AlgebraicGeometry.BoundaryFrobeniusTraces
open MathlibExt.AlgebraicGeometry.DualizingFrobeniusInterfaces
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries

section TraceSections

open MathlibExt.AlgebraicGeometry.FrobeniusTraceSections

variable {k : Type} [Field k] {n : ℕ} (V : NormalVariety k n)
  [∀ q : PrimePoint V, IsDiscreteValuationRing (LocalRing V q.val)]
  [HasDerivedPushforwards.{0}]
  (C : CanonicalWeilReference V) (D : RealWeil V) (p : ℕ) [Fact p.Prime]
  (hp : IsInCharacteristic V.X.left p)

/-- `S0` lies in the trace image of every admissible exponent. -/
example (L : V.X.left.Modules) (S : TraceSystem V C D p hp L)
    (a : AdmissibleExponent V C D p) :
    letI := S.adjoints a
    S0 V C D p hp L S ≤ sectionImage V C D p hp a.val L (S.identification a)
      (boundaryData V C D p a) (S.tensor a) (S.projection a) :=
  iInf_le _ a

/-- The local test infimum lies in every nonzero ideal compatible with all local traces. -/
example (S : TraceSystem V C D p hp (structureModule V.X.left)) (U : V.X.left.Opens)
    (A : LocalFrames V C D p hp S U) (J : Ideal Γ(V.X.left, U)) (hJ : J ≠ ⊥)
    (hc : ∀ a : AdmissibleExponent V C D p,
      letI := S.adjoints a
      AffineCartierTraceIdeals.IsCompatible
        (affineTrace V C D p hp a.val (S.identification a) (boundaryData V C D p a) (A a)) J) :
    localTestInfimum V C D p hp S U A ≤ J :=
  sInf_le ⟨hJ, hc⟩

/-- A nonzero local test infimum is compatible with every local trace. -/
example (S : TraceSystem V C D p hp (structureModule V.X.left)) (U : V.X.left.Opens)
    (A : LocalFrames V C D p hp S U) (h : localTestInfimum V C D p hp S U A ≠ ⊥)
    (a : AdmissibleExponent V C D p) :
    letI := S.adjoints a
    AffineCartierTraceIdeals.IsCompatible
      (affineTrace V C D p hp a.val (S.identification a) (boundaryData V C D p a) (A a))
      (localTestInfimum V C D p hp S U A) :=
  (localTestInfimum_isLeast V C D p hp S U A h).1.2 a

end TraceSections

section CenterDifferent

open MathlibExt.AlgebraicGeometry.FrobeniusCenterDifferent
open MathlibExt.AlgebraicGeometry.FiniteDualityModuleTrace
open MathlibExt.AlgebraicGeometry.LogResidueDifferent

variable {k : Type} [Field k] {n d : ℕ}
  {V : NormalVariety k n} {W : NormalVariety k d}
  [∀ q : PrimePoint V, IsDiscreteValuationRing (LocalRing V q.val)]
  [∀ q : PrimePoint W, IsDiscreteValuationRing (LocalRing W q.val)]
  [HasDerivedPushforwards.{0}]
  (C : CanonicalWeilReference V) (D : RealWeil V) (p e : ℕ) [Fact p.Prime]
  (hV : IsInCharacteristic V.X.left p) (hW : IsInCharacteristic W.X.left p)
  [(derivedPushforward (iterated V.X.left p hV e)).IsLeftAdjoint]
  [(derivedPushforward (iterated W.X.left p hW e)).IsLeftAdjoint]
  (F : FrobeniusIdentification V C p e hV) (I : BoundaryIndex V C p e D)
  (i : W.X ⟶ V.X)
  (comm : i.left ≫ iterated V.X.left p hV e = iterated W.X.left p hW e ≫ i.left)

/-- With `q = p^e > 1`, `(q - 1)` times the F-different is `D₀ - D_N + div(r)`. -/
example {Q : CenterDescent C D p e hV hW F I i comm} {N : CenterLine C D p e i}
    {CW : CanonicalWeilReference W} {FW : FrobeniusIdentification W CW p e hW}
    {h : IsIso (sheafPushforwardUnit (iterated W.X.left p hW e) N.cartier.line.val)}
    (R : TraceMultiplier C D p e hV hW F I i comm Q N CW FW h) (he : 0 < e) :
    ((p : ℝ) ^ e - 1) • fDifferent C D p e hV hW F I i comm R =
      realCast (canonicalTwist W CW p e) - realCast N.cartier.divisor +
        realCast (multiplierDivisor C D p e hV hW F I i comm R) := by
  have hq : (p : ℝ) ^ e - 1 ≠ 0 :=
    sub_ne_zero.mpr (one_lt_pow₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt) he.ne').ne'
  rw [fDifferent, smul_smul, mul_one_div_cancel hq, one_smul]

end CenterDifferent
