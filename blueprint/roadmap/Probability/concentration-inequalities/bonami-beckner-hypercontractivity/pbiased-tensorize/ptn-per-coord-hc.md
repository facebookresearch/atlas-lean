# $p$-biased hypercontractivity for a discrete derivative

Let $\iota$ be a finite set, let $0 < p < 1$, $0 \le \rho \le 1$ and $1 \le q \le 2$ with
$\rho^2 = 4p(1-p)(q-1)$, let $A \subseteq \{0, 1\}^\iota$ with indicator $f = \mathbf{1}_A$, and
$e \in \iota$. Then, with $\sigma = \sqrt{p(1-p)}$ and the [$p$-biased Fourier
coefficients](ptn-coeff.md) $\hat f(S)$,

$$\sum_{S \ni e} \rho^{2|S \setminus \{e\}|} \Big(\frac{\hat f(S)}{\sigma}\Big)^2 \le \mathrm{Inf}_e(f)^{2/q},$$

where $\mathrm{Inf}_e(f) = \mathbb{E}_p|f(\omega^{e \to 1}) - f(\omega^{e \to 0})|$: hypercontractivity
applied to the discrete derivative $\partial_e \mathbf{1}_A$.
