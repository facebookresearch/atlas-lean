# Threshold windows under symmetry

For every nontrivial increasing family $\mathcal{F}$ on $[n]$ invariant under a transitive group of permutations, the threshold window satisfies $p_{1-\varepsilon}(\mathcal{F}) - p_{\varepsilon}(\mathcal{F}) \le C\log(1/(2\varepsilon))/\log n$ for every $\varepsilon \in (0, 1/2)$ and an absolute constant $C$ (Friedgut-Kalai), and Bourgain-Kalai improve $\log n$ to $(\log n)^{2 - o(1)}$ for invariance under graph isomorphisms. Thus the Park-Pham theorem locates thresholds up to a $\log$ factor, while influence inequalities control the width of the window.

## Proof sketch

By the Margulis-Russo formula, $\frac{d}{dp}\mu_p(\mathcal{F})$ is the total influence; transitivity makes all influences equal, so the KKL inequality for $p$-biased measures gives total influence $\Omega(\mu_p(1-\mu_p)\log n/(p\log(2/p)))$ for $p \le 1/2$ (symmetrically for $p > 1/2$). Integrating this differential inequality bounds the window.

## Depends on

- [The Kahn-Kalai expectation threshold q(F)](kahn-kalai-expectation-threshold.md)

## Proof depends on

- [KKL inequality for $p$-biased measures](../../boolean-functions/kahn-kalai-linial-inequality/kkl-pbiased.md)

## Sources

- Ehud Friedgut, Gil Kalai, "Every monotone graph property has a sharp threshold", Proceedings of the American Mathematical Society 124 (1996) 2993-3002.
- Jean Bourgain, Gil Kalai, "Influences of variables and threshold intervals under group symmetries", Geometric and Functional Analysis 7 (1997).
- Jeff Kahn, Gil Kalai, "Thresholds and expectation thresholds", Combinatorics, Probability and Computing 16(3) (2007).
