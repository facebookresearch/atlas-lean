# Uniform stability

Let $A$ be an algorithm that maps a sample $S = (z_1, \dots, z_n) \in \mathcal{Z}^n$ to a predictor $A(S)$, and let $L(h, z)$ be the loss of a predictor $h$ at an example $z$. For $i \in \{1, \dots, n\}$ and $z' \in \mathcal{Z}$, write $S^{(i, z')}$ for the sample $S$ with its $i$-th example replaced by $z'$. The algorithm is **$\varepsilon$-uniformly stable** if for every sample $S$, index $i$, replacement $z'$ and test example $z$,

$$
L\big(A(S^{(i, z')}), z\big) - L\big(A(S), z\big) \le \varepsilon .
$$

The pairs $(S, S^{(i, z')})$ are exactly the pairs of samples that differ in at most one example. Since $S$ is itself $(S^{(i, z')})^{(i, z_i)}$, the one-sided bound of the definition also holds with the two samples exchanged, so $\lvert L(A(S^{(i, z')}), z) - L(A(S), z)\rvert \le \varepsilon$.

The definition covers algorithms without internal randomness. For a randomized algorithm, Definition 2.1 of the source takes the expectation over the internal randomness inside the supremum; this is the deterministic definition applied to the expected loss $(S, z) \mapsto \mathbb{E}_A L(A(S), z)$, which is how [the stability of SGM](is-uniformly-stable-sgm.md) is stated.

## Sources

- M. Hardt, B. Recht and Y. Singer, *Train faster, generalize better: stability of stochastic gradient descent*, ICML 2016, arXiv:1509.01240, Definition 2.1.
- O. Bousquet and A. Elisseeff, *Stability and generalization*, Journal of Machine Learning Research 2 (2002), 499–526 (uniform stability).
