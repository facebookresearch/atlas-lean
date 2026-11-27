# Differentially private learners are uniformly stable in expectation

Let $A$ be an $\varepsilon$-differentially private learning algorithm whose output hypotheses have losses in $[0,1]$. Then the randomized rule $S \mapsto \mathbb{E}_{A}[\ell(A(S), z)]$ is $(e^\varepsilon - 1)$-uniformly stable: for all samples $S, S'$ of the same size differing in one example and all points $z$,

$$
\big| \mathbb{E}[\ell(A(S), z)] - \mathbb{E}[\ell(A(S'), z)] \big| \le e^{\varepsilon} - 1 .
$$

For $(\varepsilon,\delta)$-privacy the stability parameter is $e^\varepsilon - 1 + \delta$. Hence the sharp stability bound, applied to the averaged loss $g_S(z) = \mathbb{E}_A[\ell(A(S), z)]$ with stability parameter $e^\varepsilon - 1 + \delta$, bounds with probability at least $1 - \delta'$ over the sample the generalization gap averaged over the algorithm's randomness, $\big|\mathbb{E}_A[R(A(S)) - R_{\mathrm{emp}}(A(S))]\big|$, by a quantity of order $(e^\varepsilon - 1 + \delta) \log n \log(e/\delta') + \sqrt{\log(e/\delta')/n}$, which is of order $(\varepsilon + \delta) \log n \log(e/\delta') + \sqrt{\log(e/\delta')/n}$ when $\varepsilon \le 1$, and of order $\varepsilon \log n \log(e/\delta') + \sqrt{\log(e/\delta')/n}$ for pure $(\varepsilon, 0)$-privacy with $\varepsilon \le 1$. Here $\delta'$ is the confidence parameter over the sample, distinct from the privacy parameter $\delta$, and logarithms of it are floored at $1$, as in the sharp bound.

## Proof sketch

For a $[0,1]$-valued function $f$, $\mathbb{E}[f(A(S))] = \int_0^1 \Pr[f(A(S)) > t]\,dt \le e^{\varepsilon} \int_0^1 \Pr[f(A(S')) > t]\,dt + \delta$, and symmetrically, so the expectations differ by at most $(e^\varepsilon - 1)\mathbb{E}[f(A(S'))] + \delta \le e^\varepsilon - 1 + \delta$. Apply this with $f = \ell(\cdot, z)$.

## Depends on

- [Differential privacy](../../../../cryptography/differential-privacy/differentially-private.md)
- [Uniform stability](../is-uniformly-stable.md)

## Proof depends on

- [High-probability generalization of uniformly stable algorithms with a single logarithmic factor](uniform-stability-sharp-high-probability-bound.md)

## Sources

- O. Bousquet, Y. Klochkov, N. Zhivotovskiy, "Sharper Bounds for Uniformly Stable Algorithms", COLT (2020), arXiv:1910.07833.
- V. Feldman, J. Vondrak, "High Probability Generalization Bounds for Uniformly Stable Algorithms with Nearly Optimal Rate", COLT (2019), arXiv:1902.10710, Section 4.2 and Theorem 4.10.
- R. Bassily, K. Nissim, A. Smith, T. Steinke, U. Stemmer, J. Ullman, "Algorithmic Stability for Adaptive Data Analysis", STOC (2016), arXiv:1511.02513, Lemma 3.1.
