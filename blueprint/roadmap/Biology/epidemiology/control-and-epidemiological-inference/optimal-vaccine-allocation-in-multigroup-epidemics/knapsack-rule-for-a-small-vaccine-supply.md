# Knapsack rule for a small vaccine supply

Consider the multi-group SIR model with vaccinated and unvaccinated classes, vaccination rates $U_i(t)$ capped by $\sum_i U_i(t) \le A(t)$, cumulative doses $W_i(t)$, and weighted final-size objective $H(U) = \sum_i p_i(R_i(\infty) + \kappa_i R_i^V(\infty))$, as in [Vaccinate a small vulnerable group first](vaccinate-a-small-vulnerable-group-first.md). Once vaccination has stopped, the $2n$ susceptible classes (unvaccinated and vaccinated in each group) behave as an unvaccinated $2n$-group SIR model with transmission matrix $\beta'$ built from $\beta^1, \dots, \beta^4$, recovery rates $\mu'$ and weights $p' = (p_1, \dots, p_n, \kappa_1 p_1, \dots, \kappa_n p_n)$, and its final sizes $R'_j(\infty)$ solve the multi-group final-size relations

$$S_i(\infty) = S_i(0)\exp\Big(-\sum_{j=1}^{2n} \frac{\beta'_{ij}}{\mu'_j} R'_j(\infty)\Big).$$

**Theorem.** Suppose the total supply is $B(t) \equiv \epsilon$, available immediately, $A$ is continuous with $A(0) > 0$, all other parameters are independent of $\epsilon$, and the Jacobian $Q$ of the final-size relations at the unvaccinated epidemic ($\epsilon = 0$) is invertible. Let $\tau(\epsilon) = \inf\{t : \int_0^t A = \epsilon\}$ and consider policies that use vaccine as fast as allowed. Then

$$H(U(\cdot;\epsilon)) = H(0) + y^{\top} W(\tau(\epsilon);\epsilon) + o(\epsilon),$$

where, with $x = Q^{-\top}p'$, the marginal value of one dose in group $i$ is

$$y_i = \frac{S_i(0;0)}{N_i}\,(x_{i+n} - x_i).$$

If $y$ has a unique minimal entry $y_{i^*}$, the optimal policy to leading order gives every dose to group $i^*$ at the maximal rate $A(t)$ until the supply $\epsilon$ is used.

## Depends on

- [Vaccinate a small vulnerable group first](vaccinate-a-small-vulnerable-group-first.md)

## Expansion

With a small supply, vaccination ends at time $\tau(\epsilon) = O(\epsilon)$, before the epidemic has changed appreciably, so its only effect is to move a fraction $S_i(0)/N_i$ of each dose given to group $i$ from the unvaccinated to the vaccinated susceptible class (doses go to unvaccinated people at random, and a dose given to a non-susceptible is wasted). The weighted final size is a smooth function of the initial susceptible vector, and the implicit function theorem applied to the final-size relations gives its gradient through $Q^{-1}$; the adjoint vector $x = Q^{-\top}p'$ prices one additional susceptible in each of the $2n$ classes, so moving one susceptible from class $i$ to class $i+n$ changes $H$ by $x_{i+n} - x_i$. To first order the problem is a fractional knapsack with a single capacity and linear values, whose solution puts all doses on the item with the best value per unit. A tie between groups is non-generic and is broken by any small perturbation of the parameters. The linear approximation remained accurate for supplies up to about $10\%$ of the population in an age-structured example, but the optimal start of a large campaign need not coincide with the small-supply optimum.

## Sources

- M. J. Penn, C. A. Donnelly, "Asymptotic analysis of optimal vaccination policies", Bulletin of Mathematical Biology 85 (2023) 15, Eqs. (52)–(63), Theorem 3 and its appendix proof, <https://doi.org/10.1007/s11538-022-01114-3>, PMCID PMC9859927.
