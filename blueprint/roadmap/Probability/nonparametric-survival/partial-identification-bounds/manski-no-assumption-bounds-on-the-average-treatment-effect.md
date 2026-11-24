# Manski bounds on the average treatment effect without assumptions

Let $Z \in \{0, 1\}$ be the treatment received, $Y(1), Y(0) \in [0, 1]$ potential outcomes and $Y = Y(Z)$ the observed outcome, with $0 < \Pr[Z = 1] < 1$. The observed data identify $E[Y(z) \mid Z = z]$ and $\Pr[Z = z]$ but give no information about $E[Y(z) \mid Z = 1 - z] \in [0, 1]$. Setting these unidentified terms to their extreme values in $E[Y(1) - Y(0)] = \sum_z \bigl(E[Y(1) \mid Z = z] - E[Y(0) \mid Z = z]\bigr)\Pr[Z = z]$ gives the bounds
$$E[Y(1) \mid Z = 1]\Pr[Z = 1] - E[Y(0) \mid Z = 0]\Pr[Z = 0] - \Pr[Z = 1] \le E[Y(1) - Y(0)] \le E[Y(1) \mid Z = 1]\Pr[Z = 1] - E[Y(0) \mid Z = 0]\Pr[Z = 0] + \Pr[Z = 0],$$
derived independently by Robins (1989) and Manski (1990). They are sharp: no narrower bounds follow without additional assumptions. The interval lies in $[-1, 1]$, has width exactly $1$, and always contains $0$, so without further assumptions the sign of the treatment effect cannot be determined (Richardson, Hudgens, Gilbert and Fine 2014, equations (1)–(3)). If $Y(0)$ and $Y(1)$ are unbounded the bounds are uninformative; outcomes in a bounded interval reduce to $[0, 1]$ by rescaling.

## Depends on

- [Finite-population average treatment effect](../../../Probability/nonparametric-survival/potential-outcomes-and-causal-identification/ate.md)

## Expansion

1. The model: potential outcomes with bounded outcomes, the observed law of $(Z, Y)$, and the decomposition of the average treatment effect over treatment groups.
2. The bounds from the extreme values of the unidentified conditional means.
3. Sharpness: joint laws attaining each endpoint.
4. Width $\Pr[Z = 0] + \Pr[Z = 1] = 1$ and containment of $0$.
5. Tighter bounds under monotone treatment selection or monotone treatment response, as separate statements.

## Sources

- T. S. Richardson, M. G. Hudgens, P. B. Gilbert and J. P. Fine, Nonparametric bounds and sensitivity analysis of treatment effects, Statist. Sci. 29 (2014), 596–618, Section 2.1. <https://doi.org/10.1214/14-sts499>
- Original result: C. F. Manski, Nonparametric bounds on treatment effects, Am. Econ. Rev. 80 (1990), 319–323. The bounds, their sharpness, width and containment of zero follow Richardson et al. (2014).
