/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.ModelLineMetrics
public import MathlibExt.AlgebraicGeometry.RelativePolynomialProjectivity
public import Mathlib.AlgebraicGeometry.Properties

/-!
# Analytic comparison for the actual integral-model norms

Yuan--Zhang, arXiv:2105.13587v9, A.5.1, pp238-239: model metrics on
projective integral models are continuous and invariant under domination.
The norms here are already computed from actual integral local-frame
coordinates in H(x) tensor O_x L_x. Centre, stalk-frame and ordinary
fibre-basis constructors are generic source integration inputs. These
requests do not define a height, determinant or arbitrary norm oracle.

This first local/model component treats ordinary line models (power one).
Rational tensor powers, all-place adelic coherence/completion and normalized
Deligne pairing/arithmetic-degree comparisons remain separate companions.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.IntegralModelMetrics

open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.ValuedLineFibres
open MathlibExt.AlgebraicGeometry.ModelLineMetrics

/-- The computed integral-frame norm is continuous on every local section. -/
public theorem_wanted continuousModelNorm
    (K : Type) [NormedField K] [CompleteSpace K]
    (hK : ∀ a b : K, ‖a + b‖ ≤ max ‖a‖ ‖b‖)
    (X : Over (Spec (.of K))) (L : X.left.Modules)
    (M : Model K X hK L) [IsIntegral M.scheme]
    (projective : MathlibExt.AlgebraicGeometry.RelativePolynomialProjectivity.IsProjective
      M.structureMap) (F : Frames M) : IsContinuousModelNorm M F

/-- Model metrics are invariant under domination (Yuan–Zhang, arXiv:2105.13587, A.5.1): let $K$ be a
complete non-archimedean normed field, $X$ a $K$-scheme with an $\mathcal{O}_X$-module $L$, and
$\mathcal{M}$, $\mathcal{M}'$ proper flat models of $(X, L)$ of finite presentation over the ring of
integers of $K$, each with a line bundle restricting to $L$, whose total spaces are integral and
projective over the ring of integers. Then for every map of models $\mathcal{M}' \to \mathcal{M}$
compatible with the generic fibres and the line bundles, and for any local frames used to compute
the model norms, the model norms of $\mathcal{M}$ and $\mathcal{M}'$ agree on the fibre of $L$ at
every non-archimedean point of $X$. -/
public theorem_wanted modelChangeNorm
    (K : Type) [NormedField K] [CompleteSpace K]
    (hK : ∀ a b : K, ‖a + b‖ ≤ max ‖a‖ ‖b‖)
    (X : Over (Spec (.of K))) (L : X.left.Modules)
    (M M' : Model K X hK L) [IsIntegral M.scheme] [IsIntegral M'.scheme]
    (projective : MathlibExt.AlgebraicGeometry.RelativePolynomialProjectivity.IsProjective
      M.structureMap)
    (projective' : MathlibExt.AlgebraicGeometry.RelativePolynomialProjectivity.IsProjective
      M'.structureMap) (f : ModelMap M M') (F : Frames M) (F' : Frames M') :
    ∀ (p : NonArchPoint K X) (v : Fibre K X L p.val),
      (modelNorm M F p).norm v = (modelNorm M' F' p).norm v

end WantedExt.AlgebraicGeometry.IntegralModelMetrics
