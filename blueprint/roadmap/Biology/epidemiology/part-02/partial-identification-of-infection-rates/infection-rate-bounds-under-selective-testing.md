# Infection-rate bounds under selective testing

**Setting.** In a fixed population, for a date $d$ let $C_d = 1$ if a person has been infected by $d$, $T_d = 1$ if the person has been tested by $d$ (at most once), and $R_d = 1$ if the person has received a positive result by $d$, each $0$ otherwise. Then $T_d = 0 \Rightarrow R_d = 0$ and $R_d = 1 \Rightarrow T_d = 1$. Surveillance reveals $P(T_d = 1)$ and $P(R_d = 1 \mid T_d = 1)$. Assume

- positive results are always correct, $P(C_d = 1 \mid R_d = 1) = 1$ (equivalently, specificity one on the tested subpopulation);
- credible bounds $P(C_d = 1 \mid T_d = 0) \in [L_{d0}, U_{d0}]$ on infection among the untested;
- credible bounds $P(C_d = 1 \mid T_d = 1, R_d = 0) \in [L_{d10}, U_{d10}]$, i.e. on one minus the negative predictive value.

**Proposition.** The infection rate satisfies

$$P(R_d=1) + L_{d0}\,P(T_d=0) + L_{d10}\,P(R_d=0\mid T_d=1)P(T_d=1) \;\le\; P(C_d=1) \;\le\; P(R_d=1) + U_{d0}\,P(T_d=0) + U_{d10}\,P(R_d=0\mid T_d=1)P(T_d=1),$$

with $P(R_d = 1) = P(R_d = 1\mid T_d = 1)P(T_d = 1)$. The width of the interval is

$$(U_{d10}-L_{d10})\,P(R_d=0\mid T_d=1)P(T_d=1) + (U_{d0}-L_{d0})\,P(T_d=0).$$

In particular, with no information on the untested ($U_{d0}-L_{d0}=1$) the width is at least $P(T_d = 0)$, however accurate the test; under random testing $P(C_d=1)=P(C_d=1\mid T_d=1)$, which lies in $[P(R_d=1\mid T_d=1)+L_{d10}P(R_d=0\mid T_d=1),\ P(R_d=1\mid T_d=1)+U_{d10}P(R_d=0\mid T_d=1)]$.

## Expansion

By the law of total probability, $P(C_d=1) = P(C_d=1\mid R_d=1)P(R_d=1) + P(C_d=1, R_d=0)$, and since $R_d = 0$ splits into $T_d=0$ and $\{T_d=1, R_d=0\}$,

$$P(C_d=1,R_d=0) = P(C_d=1\mid T_d=0)P(T_d=0) + P(C_d=1\mid T_d=1,R_d=0)P(R_d=0\mid T_d=1)P(T_d=1).$$

Every term other than the two unknown conditional infection rates is observed or fixed by the specificity assumption, and the expression is increasing and linear in each unknown; substituting their lower and upper bounds gives the interval, which is sharp because any pair of values in the assumed boxes is compatible with the data. The width formula shows that uncertainty about test accuracy and about infection among the untested add linearly, weighted by the tested and untested fractions.

## Sources

- C. F. Manski, F. Molinari, "Estimating the COVID-19 infection rate: anatomy of an inference problem", Journal of Econometrics 220(1) (2021) 181–192, Section 2.1, Equations 1–7, <https://doi.org/10.1016/j.jeconom.2020.04.041>, PMCID PMC7200382.
- C. F. Manski, "Anatomy of the selection problem", Journal of Human Resources 24(3) (1989) 343–360, <https://doi.org/10.2307/145818>.
