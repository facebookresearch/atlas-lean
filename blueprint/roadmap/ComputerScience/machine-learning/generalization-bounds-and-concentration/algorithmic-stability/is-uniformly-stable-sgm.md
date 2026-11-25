# SGM is uniformly stable

Under the hypotheses of [the stability bound for SGM](integral-abs-sgm-output-sub-le.md), the stochastic gradient method is $\varepsilon$-[uniformly stable](is-uniformly-stable.md) with

$$
\varepsilon = \frac{2 L^2}{n} \sum_{t=0}^{T-1} \alpha_t ,
$$

in the sense of Definition 2.1 of the source, where the expectation is over the internal randomness: for samples $S, S'$ differing in one example and every $z$, $\mathbb{E}_\kappa\, \ell(w_T(S', \kappa), z) - \mathbb{E}_\kappa\, \ell(w_T(S, \kappa), z) \le \varepsilon$. Equivalently, the randomized algorithm is the identity algorithm on samples with the loss averaged over the index sequence, $(S, z) \mapsto \mathbb{E}_\kappa\, \ell(w_T(S, \kappa), z)$.

## Sources

- M. Hardt, B. Recht and Y. Singer, *Train faster, generalize better: stability of stochastic gradient descent*, ICML 2016, arXiv:1509.01240, Theorem 3.8 with Definition 2.1.
