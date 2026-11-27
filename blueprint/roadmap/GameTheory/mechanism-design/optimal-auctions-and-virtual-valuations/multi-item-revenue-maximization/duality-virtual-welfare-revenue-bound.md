# Lagrangian duality upper bounds revenue by virtual welfare under flows

Let a Bayesian auction have finitely many bidder types $T$ with prior $f$. Call $\lambda$ a flow if $\lambda(t, t') \ge 0$ is defined for types $t$ and for $t'$ a type or the null type $\varnothing$, and flow is conserved at every type in the network where a super source sends $f(t)$ into each type $t$, each type $t$ sends $\lambda(t, t')$ to $t'$ along the incentive constraint "$t$ does not prefer to report $t'$", and the null type $\varnothing$ (the individual-rationality constraint) is the super sink. For every flow $\lambda$ define the virtual value function

$$
\Phi^\lambda_j(t) = v_j(t) - \frac{1}{f(t)} \sum_{t'} \lambda(t', t)\,\bigl(v_j(t') - v_j(t)\bigr).
$$

Then for every truthful mechanism $M$ with interim allocation $\pi$, $\mathrm{Rev}(M) \le \mathbb{E}_{t \sim f}\bigl[\sum_j \pi_j(t)\, \Phi^\lambda_j(t)\bigr]$. Equality holds iff every incentive constraint carrying positive flow binds in $M$. Hence the optimal revenue is at most the maximum expected virtual welfare under $\Phi^\lambda$ for any flow $\lambda$, with equality for an optimal dual flow; for single-item settings, a canonical flow (ironed when needed) recovers Myerson's (ironed) virtual values.

## Proof sketch

Write revenue maximization as a linear program over allocations and payments subject to individual rationality and incentive constraints between types. Its Lagrangian dual assigns multipliers $\lambda(t, t')$ to incentive and individual-rationality constraints; since payments are unconstrained, the Lagrangian is bounded only when the coefficient of every payment vanishes, which is flow conservation, and then payments drop out, leaving a virtual-welfare objective. Weak duality gives the inequality, and strong duality of linear programs gives equality at the optimum.

## Depends on

- [Bayesian incentive compatibility](../../revelation-principle/is-bayes-incentive-compatible.md)
- [Virtual valuation](../virtual-value.md)

## Proof depends on

- [Payment formula](../../myerson-s-lemma-and-revenue-equivalence/payment-formula.md)

## Sources

- Y. Cai, N. R. Devanur, S. M. Weinberg, "A Duality-Based Unified Approach to Bayesian Mechanism Design", STOC 2016; SIAM Journal on Computing 50(3) (2021), arXiv:1812.01577, Lemma 4, Definition 5 and Theorem 6.
