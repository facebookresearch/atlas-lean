/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The fundamental theorem of PAC learning: learnable iff finite VC dimension

Sources:
A. Blumer, A. Ehrenfeucht, D. Haussler and M. K. Warmuth, "Learnability and the
Vapnik-Chervonenkis dimension", Journal of the ACM 36 (1989), 929-965; S. Shalev-Shwartz and
S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University
Press (2014), Definition 3.1 and Theorem 6.7.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.MachineLearning.PACLearning.Occam
public import Cslib.MachineLearning.PACLearning.VCDimension

@[expose] public section

namespace Cslib.MachineLearning.PACLearning

/-!
# The fundamental theorem of PAC learning

Valiant's model asks for a learner that, for every distribution and every target realizable by
the class, outputs with probability at least `1 - δ` a hypothesis of error at most `ε` from
polynomially many examples (L. G. Valiant, *A theory of the learnable*, Comm. ACM 27 (1984)).
Blumer, Ehrenfeucht, Haussler and Warmuth (1989) characterized the classes of binary hypotheses
that are learnable from finitely many examples, regardless of computation, as those of finite
Vapnik-Chervonenkis dimension. In the form of Shalev-Shwartz and Ben-David (Theorem 6.7, the
equivalence of items 4 and 6), a class `H` of functions `X → {0, 1}` is PAC learnable under the
0-1 loss if and only if it has finite VC dimension.

The statement uses CSLib's notions: `IsPACLearnable` over the realizable family
`realizableFamily H` (the joint distributions under which some concept of `H` has error `0`, so
the optimal error is `0`), and `HasFiniteVCDim` built on `SetShatters`. The instance space is
countable with measurable singletons, so every set of instances and of samples is measurable; the
textbook leaves measurability implicit.
-/

/-- **The fundamental theorem of PAC learning.** On a countable instance space with measurable
singletons, a class `H` of binary hypotheses is PAC learnable over its realizable distributions
(CSLib's `IsPACLearnable H (realizableFamily H)`) if and only if it has finite VC dimension
(CSLib's `HasFiniteVCDim H`) (Blumer, Ehrenfeucht, Haussler and Warmuth, *Learnability and the
Vapnik-Chervonenkis dimension*, J. ACM 36 (1989), 929-965; Shalev-Shwartz and Ben-David,
*Understanding Machine Learning*, 2014, Theorem 6.7, equivalence of items 4 and 6). -/
public theorem_wanted isPACLearnable_realizableFamily_iff_hasFiniteVCDim {X : Type*}
    [MeasurableSpace X] [Countable X] [MeasurableSingletonClass X] (H : ConceptClass X Bool) :
    IsPACLearnable H (realizableFamily H) ↔ HasFiniteVCDim H

end Cslib.MachineLearning.PACLearning
