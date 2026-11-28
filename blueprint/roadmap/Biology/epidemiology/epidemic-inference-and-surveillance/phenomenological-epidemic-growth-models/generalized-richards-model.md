# Generalized Richards model

**Model.** The cumulative number of cases satisfies

$$C'(t) = r\,C(t)^{p}\Big[1 - \Big(\frac{C(t)}{K}\Big)^{a}\Big] \qquad \text{(Eq. 2)},$$

with growth rate $r > 0$, deceleration-of-growth parameter $p \in [0,1]$, final epidemic size $K > 0$ and shape parameter $a > 0$, started from $0 < C(0) < K$.

**Special cases.** $p = 1$ gives the Richards model $C' = rC[1 - (C/K)^a]$; $p = 1$, $a = 1$ gives the logistic equation; $K \to \infty$ gives the [generalized-growth model](generalized-growth-model.md).

**Properties.** For $0 < C(0) < K$, the solution increases strictly and tends to $K$ as $t \to \infty$; while $C \ll K$, $C' \approx rC^p$, so the early phase ranges over constant incidence ($p = 0$), polynomial growth ($0 < p < 1$) and exponential growth ($p = 1$). As a function of $C$, the incidence $C^p[1 - (C/K)^a]$ (times $r$) is maximal on $(0, K)$ where its derivative vanishes, i.e. at

$$C_{\mathrm{peak}} = K\Big(\frac{p}{p+a}\Big)^{1/a} \quad (p > 0).$$

If moreover $p > 0$ and $C(0) < C_{\mathrm{peak}}$, the incidence $C'(t)$ increases until $C(t) = C_{\mathrm{peak}}$ and decreases afterwards; otherwise (for $p = 0$, or $C(0) \ge C_{\mathrm{peak}}$) it decreases from $t = 0$.

## Depends on

- [Generalized-growth model](generalized-growth-model.md)

## Expansion

The right-hand side $g(C) = rC^p[1 - (C/K)^a]$ is positive on $(0, K)$ and vanishes at $K$, so $C$ increases monotonically to the equilibrium $K$ and cannot cross it. Incidence along the solution is $g(C(t))$, which, as a function of $C$, has derivative $rC^{p-1}[p - (p+a)(C/K)^a]$; for $p > 0$ this is positive below $C_{\mathrm{peak}}$ and negative above it, and for $p = 0$ it is negative on $(0, K)$. Since $C(t)$ increases strictly, $g(C(t))$ rises while $C(t) < C_{\mathrm{peak}}$ and falls once $C(t) > C_{\mathrm{peak}}$; a solution started at or above $C_{\mathrm{peak}}$ has decreasing incidence throughout (for example $p = a = K = 1$ and $C(0) = 0.9$). The parameter $a$ controls the asymmetry of the epidemic curve relative to the symmetric logistic curve ($a = p = 1$, peak at $K/2$).

## Sources

- G. Chowell, "Fitting dynamic models to epidemic outbreaks with quantified uncertainty: A primer for parameter uncertainty, identifiability, and forecasts", Infectious Disease Modelling 2(3) (2017) 379–398, Section 2.1.2, Eq. 2, <https://doi.org/10.1016/j.idm.2017.08.001> (PMC5726591).
- F. J. Richards, "A flexible growth function for empirical use", Journal of Experimental Botany 10 (1959) 290–300.
