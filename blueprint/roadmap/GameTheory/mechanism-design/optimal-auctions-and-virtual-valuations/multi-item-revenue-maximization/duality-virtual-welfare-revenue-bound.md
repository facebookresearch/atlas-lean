# Lagrangian duality upper bounds revenue by virtual welfare under flows

Let a Bayesian auction have finitely many bidder types $T$ with prior $f$. For every flow $\lambda$ on the directed graph of incentive constraints between types (a nonnegative function $\lambda(t, t')$ satisfying flow conservation with source the null type and sink all types), define the virtual value function

$$
\Phi^\lambda_j(t) = v_j(t) - \frac{1}{f(t)} \sum_{t'} \lambda(t', t)\,\bigl(v_j(t') - v_j(t)\bigr).
$$

Then for every truthful mechanism $M$ with interim allocation $\pi$, $\mathrm{Rev}(M) \le \mathbb{E}_{t \sim f}\bigl[\sum_j \pi_j(t)\, \Phi^\lambda_j(t)\bigr]$. Hence the optimal revenue is at most the maximum expected virtual welfare under $\Phi^\lambda$ for any flow $\lambda$, with equality for an optimal dual flow; for a single bidder with one item, a canonical flow recovers Myerson's virtual values.

## Proof sketch

Write revenue maximization as a linear program over allocations and payments subject to individual rationality and incentive constraints between types. Its Lagrangian dual assigns multipliers $\lambda(t, t')$ to incentive constraints; stationarity in payments forces $\lambda$ to be a flow, and substituting eliminates payments, leaving a virtual-welfare objective. Weak duality gives the inequality, and strong duality of linear programs gives equality at the optimum.

## Depends on

- [Bayesian incentive compatibility](../../revelation-principle/is-bayes-incentive-compatible.md)
- [Virtual valuation](../virtual-value.md)

## Proof depends on

- [Payment formula](../../myerson-s-lemma-and-revenue-equivalence/payment-formula.md)

## Sources

- Y. Cai, N. R. Devanur, S. M. Weinberg, "A Duality-Based Unified Approach to Bayesian Mechanism Design", STOC 2016; SIAM Journal on Computing 50(3) (2021), arXiv:1812.01577.
