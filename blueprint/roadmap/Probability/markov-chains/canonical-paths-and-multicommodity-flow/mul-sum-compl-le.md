# Inequality (13) for flows (hence Theorem 3′)

If every oriented edge carries at most $\rho\,\pi(u)P(u,v)$ units of a [multicommodity flow](multicommodity-flow.md), then for every set $A$ of states

$$\pi(A)\,\pi(A^c) \;\le\; \rho \sum_{u \in A,\ v \notin A} \pi(u)P(u,v).$$

This is inequality (13) of A. Sinclair, *Improved bounds for mixing rates of Markov chains and multicommodity flow*, Combinatorics, Probability and Computing 1 (1992), 351–370, which he proves for flows: the $\pi(A)\pi(A^c)$ units sent from $A$ to its complement all cross the cut. It implies his Theorem 3′, $\Phi \ge 1/(2\rho(f))$, stated set by set in [Sinclair's Theorem 3′](sum-le-two-mul.md).
