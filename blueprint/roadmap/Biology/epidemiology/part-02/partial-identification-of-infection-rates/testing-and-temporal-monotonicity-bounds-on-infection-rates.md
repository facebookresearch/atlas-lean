# Testing and temporal monotonicity bounds on infection rates

**Setting.** Use the notation and assumptions of [the selective-testing bound](infection-rate-bounds-under-selective-testing.md): indicators $C_d, T_d, R_d$, perfect specificity, and bounds $[L_{d10}, U_{d10}]$ on $P(C_d = 1 \mid T_d=1, R_d=0)$. Write $\pi_d = P(R_d=1\mid T_d=1)$ for the positivity rate among the tested.

**Testing monotonicity.** Suppose testing targets people more likely to be infected:

$$P(C_d=1\mid T_d=0) \le P(C_d=1\mid T_d=1).$$

Then one may take $L_{d0} = 0$ and

$$U_{d0} = \pi_d + U_{d10}(1-\pi_d) = U_{d10} + (1-U_{d10})\,\pi_d,$$

and the infection rate satisfies

$$B^{-}_d := P(R_d=1) + L_{d10}(1-\pi_d)P(T_d=1) \le P(C_d=1) \le B^{+}_d := P(R_d=1) + U_{d10}(1-\pi_d)P(T_d=1) + \bigl[\pi_d + U_{d10}(1-\pi_d)\bigr]P(T_d=0).$$

**Temporal monotonicity.** Infection by an earlier date implies infection by every later date, so $d' < d \Rightarrow P(C_{d'}=1) \le P(C_d = 1)$. Given date-specific bounds $B^-_{d'} \le P(C_{d'}=1) \le B^+_{d'}$ for all dates $d'$,

$$\max_{d' \le d} B^-_{d'} \;\le\; P(C_d = 1) \;\le\; \min_{d'\ge d} B^+_{d'} .$$

This interval is contained in $[B^-_d, B^+_d]$ and is strictly narrower exactly when some earlier lower bound exceeds $B^-_d$ or some later upper bound falls below $B^+_d$.

## Expansion

Testing monotonicity: the infection rate among the tested is $P(C_d=1\mid T_d=1) = \pi_d + P(C_d=1\mid T_d=1,R_d=0)(1-\pi_d) \le \pi_d + U_{d10}(1-\pi_d)$, which by the assumption bounds infection among the untested; substituting $L_{d0}=0$ and this $U_{d0}$ into the selective-testing bound gives $[B^-_d, B^+_d]$. The upper bound now depends on test accuracy through $U_{d10}$ twice, so an informative bound on the false-negative rate matters even when few people are tested.

Temporal monotonicity: date is a monotone instrumental variable. For $d' \le d$, $P(C_d=1) \ge P(C_{d'}=1) \ge B^-_{d'}$; for $d' \ge d$, $P(C_d=1) \le P(C_{d'}=1) \le B^+_{d'}$; take the best bound over each side. If people are tested more than once, reported test counts overstate $P(T_d=1)$, which makes the lower bound too high and the upper bound too low.

## Depends on

- [Infection-rate bounds under selective testing](infection-rate-bounds-under-selective-testing.md)

## Sources

- C. F. Manski, F. Molinari, "Estimating the COVID-19 infection rate: anatomy of an inference problem", Journal of Econometrics 220(1) (2021) 181–192, Section 2.2, Equations 8–13, <https://doi.org/10.1016/j.jeconom.2020.04.041>, PMCID PMC7200382.
- C. F. Manski, J. V. Pepper, "Monotone instrumental variables: with an application to the returns to schooling", Econometrica 68(4) (2000) 997–1010, Proposition 1, <https://doi.org/10.1111/1468-0262.00144>.
