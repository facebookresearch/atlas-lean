# Globalness is equivalent to small generalized influences

Let $f : (\{0,1\}^n, \mu_p) \to \mathbb{R}$ and $r \ge 1$. If $f$ is $(r, \varepsilon)$-global, then $I_S(f) \le 4^{|S|}\varepsilon^2$ for every $|S| \le r$. Conversely, if $I_S(f) \le \delta$ for all $1 \le |S| \le r$ and $\|f\|_2 \le \delta^{1/2}$, then every restriction $f_{S \to x}$ with $|S| \le r$ satisfies $\|f_{S \to x}\|_2^2 \le 2^{O(r)}\delta$, where the generalized influences are taken in the $p$-biased normalization above. Thus the hypothesis of global hypercontractivity may be stated either via restrictions or via generalized influences.

## Proof sketch

Write $E_S f = \sum_{x \in \{0,1\}^S} (-1)^{|S|-|x|} f_{S \to x}$, so that $I_S(f) = \|E_S f\|_2^2$. Its $2^{|S|}$ coefficients are $\pm 1$, so the triangle inequality gives $\sqrt{I_S(f)} \le \sum_x \|f_{S \to x}\|_2 \le 2^{|S|}\varepsilon$. Conversely, for $i \notin S$ write $g = E_S f$; then $E_S(f_{i \to a}) = g_{i \to a}$ and $g_{i \to a}$ is the $\mu_p$-average of $g$ over coordinate $i$ plus $\pm(1-p)$ or $\pm p$ times $E_{S \cup \{i\}} f$, so $\|E_S(f_{i \to a})\|_2 \le \|E_S f\|_2 + \|E_{S \cup \{i\}} f\|_2$ by Jensen. Inducting on the restricted coordinates bounds $\|f_{S \to x}\|_2$ by a sum of $2^{|S|}$ terms $\sqrt{I_U(f)}$ with $U \subseteq S$ (and $\|f\|_2$ for $U = \emptyset$).

## Depends on

- [Global functions on the p-biased cube](pbiased-global-function.md)

## Sources

- P. Keevash, N. Lifshitz, E. Long, D. Minzer, "Hypercontractivity for global functions and sharp thresholds", Journal of the American Mathematical Society 37 (2024), arXiv:1906.05568.
