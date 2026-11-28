# Smoothed regret bounds depending on VC dimension and bracketing numbers

Let $H$ be a binary class of VC dimension $d$ and $\sigma \in (0,1]$.

- Against a non-adaptive sequence of $\sigma$-smooth distributions (with respect to the uniform measure $U$ on $X$) there is an algorithm with expected regret $O\big(\sqrt{d\, T \log(T/\sigma)}\big)$.
- Against an adaptive sequence of $\sigma$-smooth distributions with respect to the uniform measure $U$ on $X$, there is an algorithm with expected regret $O\Big(\sqrt{T \log N_{[\,]}\big(H, U, \tfrac{\sigma}{4\sqrt{T}}\big)}\Big)$, where $N_{[\,]}(H, U, \epsilon)$ is the $\epsilon$-bracketing number of $H$.

For halfspaces in $\mathbb{R}^d$, $N_{[\,]}(H,\mu,\epsilon) \le (d/\epsilon)^{O(d)}$ for every measure $\mu$, giving regret $\tilde O(\sqrt{dT\log(T/\sigma)})$ even though halfspaces have infinite Littlestone dimension. Analogous bounds hold for the error of differentially private query release under smoothed data.

## Proof sketch

Run multiplicative weights over a finite cover of $H$. Against non-adaptive smooth sequences, the instances are dominated by product-like measures and an $\epsilon$-cover in $L_1(\mu)$ of size $(1/\epsilon)^{O(d)}$ suffices, since a smooth instance falls in the disagreement region of two $\epsilon$-close hypotheses with probability at most $\epsilon/\sigma$. Adaptivity breaks this argument, and brackets (pairs of functions sandwiching each hypothesis) restore it because the expected number of instances inside any bracket is controlled by smoothness regardless of adaptivity.

## Depends on

- [Smoothed adversaries in online learning](smoothed-adversary.md)

## Proof depends on

- [The $\sqrt{T}$ regret bound of Hedge](../hedge-algorithm/regret-le-two-sqrt.md)
- [Sauer bound for the growth function](../../../not-yet-classified/growth-function/growth-function-le-sum.md)

## Sources

- N. Haghtalab, T. Roughgarden, A. Shetty, "Smoothed Analysis of Online and Differentially Private Learning", NeurIPS (2020), arXiv:2006.10129, Theorems 3.1, 3.3 and 3.4.
