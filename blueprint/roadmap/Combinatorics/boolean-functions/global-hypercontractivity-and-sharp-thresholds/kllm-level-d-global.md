# Level-d inequality for global sets of small measure

There is an absolute constant $C > 0$ such that the following holds for every $0 < p < 1$. Let $\mathcal{A} \subseteq \{0,1\}^n$ have $\mu_p(\mathcal{A}) = \alpha$, let $r > 1$, and let $d \ge 1$ be an integer with $d \le \frac{1}{4}\log(1/\alpha)$. If $\mu_p(\mathcal{A}_{S \to x}) \le r^{|S|}\alpha$ for all $S$ with $|S| \le d$ and all $x \in \{0,1\}^S$, then the Fourier weight of $\mathcal{A}$ on level $d$ satisfies

$$
\sum_{|T| = d} \hat{1}_{\mathcal{A}}(T)^2 \le \alpha^2 \left( \frac{C r^2 \log(1/\alpha)}{d} \right)^{d}.
$$

## Proof sketch

Apply global hypercontractivity in $L^q$ to the low-degree projection $g = 1_{\mathcal{A}}^{\le d}$: Hölder gives $\|g\|_2^2 = \langle g, 1_{\mathcal{A}} \rangle \le \|g\|_q\, \alpha^{1 - 1/q}$, the global $(2, q)$-hypercontractive inequality bounds $\|g\|_q$ by $q^{O(d)}$ times a quantity controlled by the globalness of $\mathcal{A}$, and choosing $q \approx \log(1/\alpha)$ yields the bound; this needs the sharp global hypercontractive inequality of Keller, Lifshitz and Marcus, since that of Keevash et al. gives $\log^3(1/\alpha)$ in place of $\log(1/\alpha)$.

## Depends on

- [Global functions on the p-biased cube](pbiased-global-function.md)

## Proof depends on

- [Keevash–Lifshitz–Long–Minzer: hypercontractivity for global functions](kllm-global-hypercontractivity.md)
- [Level-1 Inequality](../structure-theorems-for-boolean-functions/level-one-inequality.md)

## Sources

- P. Keevash, N. Lifshitz, E. Long, D. Minzer, "Hypercontractivity for global functions and sharp thresholds", Journal of the American Mathematical Society 37 (2024), arXiv:1906.05568.
- N. Keller, N. Lifshitz, O. Marcus, "Sharp hypercontractivity for global functions", arXiv:2307.01356.
