# Lagrangian duality upper bounds revenue by virtual welfare under flows

Let a Bayesian auction with additive bidders have, for each bidder $i$, a finite type set $T_i$ of value vectors $t_i = (v_{i1}(t_i), \dots, v_{im}(t_i))$ drawn independently from a prior $f_i$ with $f_i(t_i) > 0$ for every $t_i \in T_i$, and add a null type $\varnothing$ with $\pi_i(\varnothing) = 0$ and $p_i(\varnothing) = 0$, so that reporting $\varnothing$ stands for not participating. A mechanism $M$ is described by its interim allocation $\pi_{ij}(t_i)$ and interim payment $p_i(t_i)$; it is Bayesian incentive compatible and interim individually rational (BIC and BIR) if $\pi_i(t_i) \cdot t_i - p_i(t_i) \ge \pi_i(t_i') \cdot t_i - p_i(t_i')$ for all $i$, $t_i \in T_i$ and $t_i' \in T_i \cup \{\varnothing\}$. For each bidder $i$, call $\lambda_i$ a flow if $\lambda_i(t, t') \ge 0$ is defined for $t \in T_i$ and $t' \in T_i \cup \{\varnothing\}$, and flow is conserved at every type in the network where a super source sends $f_i(t)$ into each type $t$, each type $t$ sends $\lambda_i(t, t')$ to $t'$ along the constraint "$t$ does not prefer to report $t'$", and the null type $\varnothing$ (the individual-rationality constraint) is the super sink. For every family $\lambda = (\lambda_i)_i$ of such flows define the virtual value functions

$$
\Phi^\lambda_{ij}(t_i) = v_{ij}(t_i) - \frac{1}{f_i(t_i)} \sum_{t' \in T_i} \lambda_i(t', t_i)\,\bigl(v_{ij}(t') - v_{ij}(t_i)\bigr).
$$

Then every BIC and BIR mechanism $M$ satisfies $\mathrm{Rev}(M) = \sum_i \sum_{t_i} f_i(t_i)\, p_i(t_i) \le \sum_i \sum_{t_i} f_i(t_i) \sum_j \pi_{ij}(t_i)\, \Phi^\lambda_{ij}(t_i)$, the expected virtual welfare of $\pi$; for a single bidder this reads $\mathrm{Rev}(M) \le \mathbb{E}_{t \sim f}\bigl[\sum_j \pi_j(t)\, \Phi^\lambda_j(t)\bigr]$. Equality holds iff every constraint carrying positive flow binds in $M$. Hence the optimal BIC and BIR revenue is at most the maximum expected virtual welfare under $\Phi^\lambda$ over feasible interim allocations, for any family of flows $\lambda$, with equality for an optimal dual solution; for single-item settings, a canonical flow (ironed when needed) recovers Myerson's (ironed) virtual values.

## Proof sketch

Write revenue maximization as a linear program over allocations and payments subject to individual rationality and incentive constraints between types. Its Lagrangian dual assigns multipliers $\lambda_i(t, t')$ to the incentive and individual-rationality constraints of each bidder; since payments are unconstrained, the Lagrangian is bounded only when the coefficient of every payment vanishes, which is flow conservation, and then payments drop out, leaving a virtual-welfare objective. Weak duality gives the inequality, and strong duality of linear programs gives equality at the optimum.

## Depends on

- [Bayesian incentive compatibility](../../revelation-principle/is-bayes-incentive-compatible.md)
- [Virtual valuation](../virtual-value.md)

## Proof depends on

- [Payment formula](../../myerson-s-lemma-and-revenue-equivalence/payment-formula.md)
- [Strong linear programming duality](../../../../Geometry/convex-geometry/linear-programming/strong-linear-programming-duality.md)

## Sources

- Y. Cai, N. R. Devanur, S. M. Weinberg, "A Duality-Based Unified Approach to Bayesian Mechanism Design", STOC 2016; SIAM Journal on Computing 50(3) (2021), arXiv:1812.01577, Lemma 4, Definition 5 and Theorem 6.
