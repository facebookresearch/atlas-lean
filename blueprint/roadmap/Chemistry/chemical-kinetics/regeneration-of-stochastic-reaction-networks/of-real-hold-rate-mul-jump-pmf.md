# Rate-weighted jump kernel of a stochastic reaction network

Let $M$ be a [stochastic reaction network](../non-explosion-of-stochastic-reaction-networks/stochastic-crn.md) with finite sets $S$ of
species and $\rho$ of reactions: propensities $\lambda_r(x) \ge 0$ that vanish when the state $x$
lacks the reactants of $r$. Let $\lambda(x) = \sum_r \lambda_r(x)$ be the
[total propensity](../non-explosion-of-stochastic-reaction-networks/total-rate.md), $q(x)$ the [holding rate](../non-explosion-of-stochastic-reaction-networks/hold-rate.md)
($\lambda(x)$ if $\lambda(x) > 0$, and $1$ at an absorbing state, $\lambda(x) = 0$), and $K$ the
[jump kernel](../non-explosion-of-stochastic-reaction-networks/jump-pmf.md). Then for all states $x, y \in \mathbb{N}^S$

$$q(x)\, K(x, y) = \sum_{r \,:\, x - \mathrm{src}(r) + \mathrm{prod}(r) = y} \lambda_r(x) +
\mathbf{1}\{\lambda(x) = 0 \text{ and } x = y\},$$

with the subtraction truncated at $0$ in each coordinate. The first term is the total propensity
of the reactions leading from $x$ to $y$; the second is the fictitious self-loop of an absorbing
state, which jumps to itself at rate $1$.
