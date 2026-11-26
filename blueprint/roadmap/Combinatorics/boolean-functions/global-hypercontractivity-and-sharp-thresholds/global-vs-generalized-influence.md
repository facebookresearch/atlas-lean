# Globalness is equivalent to small generalized influences

Let $f : (\{0,1\}^n, \mu_p) \to \mathbb{R}$ and $r \ge 1$. If $f$ is $(r, \varepsilon)$-global, then $I_S(f) \le 4^{|S|}\varepsilon^2$ for every $|S| \le r$. Conversely, if $I_S(f) \le \delta$ for all $1 \le |S| \le r$ and $\|f\|_2 \le \delta^{1/2}$, then every restriction $f_{S \to x}$ with $|S| \le r$ satisfies $\|f_{S \to x}\|_2^2 \le 2^{O(r)}\delta$, where the generalized influences are taken in the $p$-biased normalization above. Thus the hypothesis of global hypercontractivity may be stated either via restrictions or via generalized influences.

## Proof sketch

The generalized derivative $D_S f$ is a signed combination of the $2^{|S|}$ restrictions $f_{S \to x}$ with coefficients bounded by $1$ after normalization, so the triangle inequality bounds $I_S(f)$ by restriction norms. Conversely, a restriction is recovered from derivatives by the inverse Möbius-type expansion over subsets of $S$, again with $2^{O(|S|)}$ terms.

## Depends on

- [Global functions on the p-biased cube](pbiased-global-function.md)

## Sources

- P. Keevash, N. Lifshitz, E. Long, D. Minzer, "Hypercontractivity for global functions and sharp thresholds", Journal of the American Mathematical Society 37 (2024), arXiv:1906.05568.
