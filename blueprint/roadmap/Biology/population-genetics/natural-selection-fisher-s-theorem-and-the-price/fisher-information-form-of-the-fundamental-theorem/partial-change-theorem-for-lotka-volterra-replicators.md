# Partial-change theorem for Lotka–Volterra replicators

Let $P_1(t), \dots, P_n(t) > 0$ be differentiable and satisfy the Lotka–Volterra equations

$$\frac{dP_i}{dt} = f_i(P_1, \dots, P_n)\,P_i, \qquad i = 1, \dots, n,$$

for continuous fitness functions $f_i : [0, \infty)^n \to \mathbb{R}$. Put $p_i = P_i/\sum_j P_j$, mean fitness $\bar f = \sum_j p_j f_j(P)$ and variance in fitness $\operatorname{Var}(f) = \sum_j p_j (f_j(P) - \bar f)^2$. Then the frequencies obey the replicator equation

$$\dot p_i = \bigl(f_i(P) - \bar f\bigr)\,p_i,$$

and the part of the change in mean fitness due to changing frequencies equals the variance in fitness:

$$\sum_{i=1}^n \dot p_i\, f_i\bigl(P(t)\bigr) = \operatorname{Var}(f).$$

The total rate of change is $\dot{\bar f} = \operatorname{Var}(f) + \sum_i p_i\,\frac{d}{dt}f_i(P(t))$, so $\dot{\bar f} = \operatorname{Var}(f) \ge 0$ only when the second (environmental) term vanishes, for instance when the $f_i$ are constant.

## Depends on

- [From Lotka–Volterra densities to replicator frequencies](../../../population-dynamics/replicator-and-lotka-volterra-equivalence/of-lv.md)
- [Fisher's fundamental theorem of natural selection](../mean-fitness-select-sub.md)

## Expansion

The quotient rule and the Lotka–Volterra equations give $\dot p_i = f_i p_i - p_i\sum_j f_j p_j$, the replicator equation. Then $\sum_i f_i\dot p_i = \sum_i f_i(f_i - \bar f)p_i$, and subtracting $\bar f\sum_i (f_i - \bar f)p_i = 0$ gives $\sum_i (f_i - \bar f)^2 p_i$. This is the reading of Fisher's theorem advocated by Price and Ewens: only the frequency-change term equals the variance, and it carries no guarantee that mean fitness increases.

## Sources

- J. C. Baez, "The fundamental theorem of natural selection", Entropy 23 (2021) 1436, <https://doi.org/10.3390/e23111436>, PMCID PMC8624378. Section 2, Equations (1)–(8) and Theorem 1.
