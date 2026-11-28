# Globalness is equivalent to small generalized influences

Let $p \le 1/2$, $r \ge 1$ and $\delta > 0$, and let $f : \{0,1\}^n \to \{0,1\}$ with the $p$-biased measure $\mu_p$, generalized influences $I_S(f)$ as above, and $J \to 1$ denoting the restriction fixing every coordinate of $J$ to $1$. Say that $f$ is *$(r, \delta)$-measure-global* if $\mu_p(f_{J \to 1}) \le \mu_p(f) + \delta$ for every $J \subseteq [n]$ with $|J| \le r$. If $f$ is $(r, \delta)$-measure-global and $\mu_p(f) \le \delta$, then $I_S(f) \le 8^r\delta$ for every $S$ with $|S| \le r$; if $f$ is monotone and $(r, \delta)$-measure-global, then $I_S(f) \le 8^r\delta$ for every nonempty $S$ with $|S| \le r$. Conversely, if $I_S(f) \le \delta$ for every nonempty $S$ with $|S| \le r$, then $f$ is $(r, 9^r\delta)$-measure-global. Thus, for Boolean functions, the hypothesis of global hypercontractivity may be stated either via restrictions or via generalized influences.

## Proof sketch

For Boolean $f$, $\|f_{S \to x}\|_2^2 = \mu_p(f_{S \to x})$. If $J$ is the set of coordinates where $x$ is $1$, then $\mu_p(f_{S \to x}) \le (1-p)^{-|S \setminus J|}\mu_p(f_{J \to 1}) \le 2^{|S|} \cdot 2\delta$ by globalness, $\mu_p(f) \le \delta$ and $p \le 1/2$. Writing $\sqrt{I_S(f)}$ as the norm of the alternating sum of the $2^{|S|}$ restrictions $f_{S \to x}$ and applying the triangle inequality bounds $I_S(f)$ by $2^{O(|S|)}\delta$; KLLM's bookkeeping gives $8^r$, and for monotone $f$ they remove the hypothesis $\mu_p(f) \le \delta$. Conversely, let $\Delta_T f = \sum_{x \in \{0,1\}^T} (-1)^{|T|-|x|} f_{T \to x}$, so that $I_T(f) = \|\Delta_T f\|_2^2$. Expanding $f_{i \to 1} = \mathbb{E}_i f + (1-p)\Delta_{\{i\}} f$ over $i \in J$ gives $\mu_p(f_{J \to 1}) - \mu_p(f) = \sum_{\emptyset \ne T \subseteq J} (1-p)^{|T|}\,\mathbb{E}[\Delta_T f]$. Since $\Delta_T f$ is integer-valued, $|\mathbb{E}[\Delta_T f]| \le \mathbb{E}[(\Delta_T f)^2] = I_T(f) \le \delta$, so the difference is at most $2^{r}\delta \le 9^r\delta$.

## Depends on

- [Global functions on the p-biased cube](pbiased-global-function.md)

## Sources

- P. Keevash, N. Lifshitz, E. Long, D. Minzer, "Hypercontractivity for global functions and sharp thresholds", Journal of the American Mathematical Society 37 (2024) 245-279, arXiv:1906.05568, Definition 4.1 and Lemmas 4.2, 4.3 and 4.5.
