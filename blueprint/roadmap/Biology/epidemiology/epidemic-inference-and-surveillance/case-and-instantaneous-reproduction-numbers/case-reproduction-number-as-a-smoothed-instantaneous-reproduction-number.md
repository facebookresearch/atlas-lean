# Case reproduction number as a smoothed instantaneous reproduction number

**Model.** Let $I(t)$ be the mean incidence of infection at calendar time $t$ in a large population (no susceptible depletion), and let $\beta(t, \tau) \ge 0$ be the infectiousness, at calendar time $t$, of an individual infected a time $\tau$ earlier, so that incidence follows the renewal equation

$$I(t) = \int_0^\infty \beta(t, \tau)\, I(t - \tau)\, d\tau .$$

Define the **case reproduction number** $R_c(t) = \int_0^\infty \beta(t + \tau, \tau)\, d\tau$ (the expected number infected by someone infected at $t$) and the **instantaneous reproduction number** $R(t) = \int_0^\infty \beta(t, \tau)\, d\tau$ (the number they would infect if conditions stayed as at time $t$).

**Proposition.** Suppose infectiousness is separable, $\beta(t, \tau) = \Phi_1(t)\Phi_2(\tau)$ with $\Phi_2 \ge 0$ integrable and normalized, $w(\tau) := \Phi_2(\tau)$, $\int_0^\infty w = 1$. Then:

1. $\beta(t,\tau) = R(t)\, w(\tau)$, so $w$ is the generation-time density;
2. $R(t) = \dfrac{I(t)}{\int_0^\infty I(t - \tau)\, w(\tau)\, d\tau}$ whenever the denominator is positive;
3. $R_c(t) = \int_0^\infty R(t + \tau)\, w(\tau)\, d\tau$, a forward moving average of $R$ weighted by $w$;
4. if $I(t) = I(0) e^{r t}$ with $\int_0^\infty e^{-r\tau} w(\tau)\, d\tau < \infty$, then $R(t) = R_c(t) = 1/\int_0^\infty e^{-r\tau} w(\tau)\, d\tau$.

For incidence reported in bins, with $w_j$ the generation-time mass at lag $j$, item 2 becomes $R_t = I_t / \sum_{j \ge 1} I_{t-j} w_j$ and item 3 becomes $R_{c,t} = \sum_{j \ge 1} w_j R_{t+j} = \sum_{j \ge 1} w_j \, I_{t+j} \big/ \sum_{l \ge 1} I_{t+j-l} w_l$.

## Depends on

- [Reproductive number from growth rate and generation interval](../../euler-lotka-equation-and-the-reproduction-number/reproduction-number.md)

## Expansion

Integrating $\beta(t,\tau) = \Phi_1(t)w(\tau)$ over $\tau$ gives $\Phi_1(t) = R(t)$, which is item 1; substituting into the renewal equation and solving for $R(t)$ gives item 2. Item 3 is $R_c(t) = \int \beta(t + \tau, \tau)\, d\tau = \int R(t+\tau) w(\tau)\, d\tau$. Under exponential growth item 2 gives $R(t) = e^{rt}/\int e^{r(t-\tau)}w(\tau)\,d\tau$, which is constant, so item 3 returns the same constant. An abrupt drop in transmission at time $t_I$ makes $R(t)$ jump at $t_I$ while $R_c(t)$ declines smoothly before $t_I$, because people infected earlier spend part of their infectious period after it. The estimator of $R_c$ uses future incidence and so is right-censored in real time, while the estimator of $R$ uses only past incidence. The source also shows that heterogeneous, non-inherited natural histories $X \sim f$ leave the renewal equation unchanged once $\beta$ is replaced by its average $\int \beta(X, t, \tau) f(X)\, dX$.

## Sources

- C. Fraser, *Estimating individual and household reproduction numbers in an emerging epidemic*, PLoS ONE (2007). <https://doi.org/10.1371/journal.pone.0000758> (PMCID: PMC1950082). Methods, Equations (1)–(12) and (22)–(39).
- J. Wallinga and M. Lipsitch, *How generation intervals shape the relationship between growth rates and reproductive numbers*, Proceedings of the Royal Society B (2007). <https://doi.org/10.1098/rspb.2006.3754>
