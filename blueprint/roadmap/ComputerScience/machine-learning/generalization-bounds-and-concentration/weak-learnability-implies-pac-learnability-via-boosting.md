# Weak learnability implies PAC learnability via boosting

Let $B$ be a base class of binary classifiers with $\mathrm{VCdim}(B) = d$ and let $H$ be $\gamma$-weakly learnable
by an oracle that, for every distribution on a sample, returns with probability at least $1 - \delta_0$ a member of
$B$ with weighted error at most $1/2 - \gamma$. AdaBoost run for $T = \lceil \log(2/\varepsilon)/(2\gamma^2) \rceil$
rounds on $m$ examples outputs, with probability at least $1 - T\delta_0$, a weighted vote in the class
$L(B, T)$ of sign-of-linear-combination classifiers of $T$ members of $B$, whose training error is at most
$e^{-2\gamma^2 T} \le \varepsilon/2$. Since $\mathrm{VCdim}(L(B,T)) = O(T d \log(T d))$, the fundamental theorem of
PAC learning gives that $H$ is PAC learnable in the realizable setting with sample size polynomial in
$1/\gamma$, $d$, $1/\varepsilon$ and $\log(1/\delta)$, splitting the confidence budget between the oracle calls and
uniform convergence by a union bound.

## Expansion

This node states a precise result. A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: VC dimension of a class of binary functions.
- Statement prerequisite: $\gamma$-weak learnability with a weak-learning oracle.

- Proof prerequisite: Sauer-Shelah-Perles lemma.

## Proof depends on

- [AdaBoost drives the training error down exponentially](../online-learning-and-boosting/adaboost/train-err-le-exp.md)
- [VC classes have uniform convergence (upper half of the quantitative fundamental theorem)](vc-and-natarajan-classes/vc-classes-have-uniform-convergence.md)

## Sources

- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press, 2014 (author copy), Definition 10.1 (weak learnability), Theorem 10.2 (training error of AdaBoost at most $e^{-2\gamma^2 T}$), Lemma 10.3 ($\mathrm{VCdim}(L(B,T)) \le T(d+1)(3\log(T(d+1)) + 2)$) and Section 10.4. <https://www.cs.huji.ac.il/~shais/UnderstandingMachineLearning/understanding-machine-learning-theory-algorithms.pdf>
