# H-Delta-H divergence and domain adaptation bound

Let $D_S$ and $D_T$ be source and target distributions on $X \times \{0,1\}$ with marginals $D_S^X$, $D_T^X$, and
let $H$ be a class of binary classifiers with VC dimension $d$. Write $\varepsilon_S(h)$, $\varepsilon_T(h)$ for the
labelled errors, $d_{H\Delta H}(D_S^X, D_T^X) = 2 \sup_{h, h' \in H} \lvert \Pr_{D_S^X}(h \ne h') - \Pr_{D_T^X}(h \ne h') \rvert$
and $\lambda = \inf_{h \in H} (\varepsilon_S(h) + \varepsilon_T(h))$. Then for every $h \in H$,
$\varepsilon_T(h) \le \varepsilon_S(h) + \tfrac12 d_{H\Delta H}(D_S^X, D_T^X) + \lambda$. If $U_S$ and $U_T$ are unlabelled
samples of size $m \ge 1$ from the two marginals, then with probability at least $1 - \delta$, for every $h \in H$,
$\varepsilon_T(h) \le \varepsilon_S(h) + \tfrac12 \hat d_{H\Delta H}(U_S, U_T) + 4\sqrt{(2d\log(2m) + \log(2/\delta))/m} + \lambda$
(Ben-David et al., Theorem 2), under the measurability conditions needed for the suprema.

## Expansion

This node states a precise result. A good expansion adds a page for the pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: VC dimension of a class of binary functions.

## Depends on

- [The 0-1 loss as an abstract loss](../pac-learning/risk-of-the-0-1-loss/zero-one-loss.md)

## Proof depends on

- [VC classes have uniform convergence (upper half of the quantitative fundamental theorem)](../generalization-bounds-and-concentration/vc-and-natarajan-classes/vc-classes-have-uniform-convergence.md)

## Sources

- S. Ben-David, J. Blitzer, K. Crammer, A. Kulesza, F. Pereira and J. W. Vaughan, *A theory of learning from different domains*, Machine Learning 79 (2010) 151–175: Lemma 3, Theorem 2 and its proof (the deterministic bound from Lemma 3 and the triangle inequality), and Lemma 1. <https://www.alexkulesza.com/pubs/adapt_mlj10.pdf>
