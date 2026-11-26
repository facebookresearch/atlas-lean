# Level-d inequality for global sets of small measure

For every $d \ge 1$ there are $C_d, c_d > 0$ such that the following holds for every $0 < p \le 1/2$. If $\mathcal{A} \subseteq \{0,1\}^n$ has $\mu_p(\mathcal{A}) = \alpha$ and $\mu_p(\mathcal{A}_{S \to x}) \le \alpha^{1 - c_d}$ for all $S$ with $|S| \le d$ and all $x \in \{0,1\}^S$, then its Fourier weight on levels $1$ through $d$ satisfies

$$
\sum_{1 \le |T| \le d} \hat{1}_{\mathcal{A}}(T)^2 \le C_d\, \alpha^2 \log^{d}(1/\alpha).
$$

## Proof sketch

Apply global hypercontractivity to the low-degree projection $g = 1_{\mathcal{A}}^{\le d}$: the Hölder inequality $\|g\|_2^2 = \langle g, 1_{\mathcal{A}} \rangle \le \|g\|_4 \alpha^{3/4}$ combined with $\|g\|_4^4 \le C^d \delta \|g\|_2^2$, where globalness of $\mathcal{A}$ bounds the generalized influences $\delta$ of $g$, yields the level-$d$ bound after optimizing the noise parameter.

## Depends on

- [Global functions on the p-biased cube](pbiased-global-function.md)

## Proof depends on

- [Keevash–Lifshitz–Long–Minzer: hypercontractivity for global functions](kllm-global-hypercontractivity.md)
- [Level-1 Inequality](../structure-theorems-for-boolean-functions/level-one-inequality.md)

## Sources

- P. Keevash, N. Lifshitz, E. Long, D. Minzer, "Hypercontractivity for global functions and sharp thresholds", Journal of the American Mathematical Society 37 (2024), arXiv:1906.05568.
