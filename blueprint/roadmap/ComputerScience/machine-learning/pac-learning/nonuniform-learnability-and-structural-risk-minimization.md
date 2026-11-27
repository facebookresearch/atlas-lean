# Nonuniform learnability and structural risk minimization

For binary classification with the $0$-$1$ loss, a class $\mathcal{H}$ is nonuniformly learnable if and only
if it is a countable union of agnostic PAC learnable classes.

Let $\mathcal{H} = \bigcup_{n \ge 1} \mathcal{H}_n$ where each $\mathcal{H}_n$ has the uniform convergence property
with sample complexity $m^{UC}_{\mathcal{H}_n}$, and let
$\varepsilon_n(m,\delta) = \min\{\varepsilon \in (0,1) : m^{UC}_{\mathcal{H}_n}(\varepsilon, \delta) \le m\}$, assuming this
minimum exists. Let $w : \mathbb{N} \to (0,1]$ satisfy $\sum_n w(n) \le 1$. Then for every $\delta \in (0,1)$, with
probability at least $1-\delta$, for all $n$ and all $h \in \mathcal{H}_n$,
$|L_\mathcal{D}(h) - L_S(h)| \le \varepsilon_n(m, w(n)\delta)$. With the weights $w(n) = 6/(\pi^2 n^2)$, the structural
risk minimization rule, which minimizes $L_S(h) + \varepsilon_{n(h)}(m, w(n(h))\delta)$ with
$n(h) = \min\{n : h \in \mathcal{H}_n\}$, is a nonuniform learner with sample complexity
$m^{NUL}(\varepsilon, \delta, h) \le m^{UC}_{\mathcal{H}_{n(h)}}(\varepsilon/2, w(n(h))\delta)$.

## Expansion

This node states a precise result. A good expansion adds a page for each of the following
prerequisites and links it under the dependency sections below:

- Statement prerequisite: Nonuniform learnability and nonuniform learners for binary classification with the 0-1 loss.

## Depends on

- [Learners and agnostic PAC learnability](agnostic-pac-learning-and-uniform-convergence/learners-and-agnostic-pac-learnability.md)
- [Uniform convergence property and eps-representative samples](agnostic-pac-learning-and-uniform-convergence/uniform-convergence-property-and-eps-representative-samples.md)

## Proof depends on

- [VC classes have uniform convergence (upper half of the quantitative fundamental theorem)](../generalization-bounds-and-concentration/vc-and-natarajan-classes/vc-classes-have-uniform-convergence.md)
- [Shattering lower bound for PAC learning](../generalization-bounds-and-concentration/shattering-lower-bound-for-pac-learning.md)

## Sources

- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press, 2014 (author copy), Theorem 7.2, Theorem 7.4, equation (7.1) and Theorem 7.5. <https://www.cs.huji.ac.il/~shais/UnderstandingMachineLearning/understanding-machine-learning-theory-algorithms.pdf>
