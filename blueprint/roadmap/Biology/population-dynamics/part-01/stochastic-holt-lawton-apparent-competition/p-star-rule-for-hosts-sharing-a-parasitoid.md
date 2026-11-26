# $P^*$ rule for hosts sharing a parasitoid

**Setting.** In the stochastic Holt–Lawton host–parasitoid model with $k \ge 2$ host species,

$$x_i(t+1) = R_i(t)\, x_i(t)\, e^{-a_i(t) y(t)}, \qquad y(t+1) = \sum_{i=1}^k x_i(t)\big(1 - e^{-a_i(t) y(t)}\big) + I(t),$$

assume the fecundities $R_i(t)$, attack rates $a_i(t)$ and parasitoid immigration $I(t)$ are i.i.d. in time with values in compact subintervals of $(0,\infty)$ (assumptions A1–A3). For each host define

$$P_i^* := \frac{\mathbb{E}[\ln R_i(t)]}{\mathbb{E}[a_i(t)]},$$

the mean parasitoid density that host $i$ alone would sustain at stationarity.

**Theorem.** Suppose every host can invade the parasitoid-only state, $\mathbb{E}[\ln R_i(t)] > \mathbb{E}[a_i(t)]\,\mathbb{E}[I(t)]$ for $i = 1, \dots, k$, and that $P_1^* > P_i^*$ for all $i = 2, \dots, k$. If $\prod_{i=1}^k x_i(0) > 0$, then there are $\alpha, \beta > 0$ such that

$$\limsup_{t \to \infty} \frac1t \ln \max_{2 \le i \le k} x_i(t) < 0 \ \text{ a.s.},$$

and host $1$ persists stochastically: for $\delta \le 1$,

$$\limsup_{t\to\infty} \frac{\#\{1 \le s \le t : x_1(s) \le \delta\}}{t} \le \alpha\delta^\beta \ \text{ a.s.}, \qquad \limsup_{t \to \infty} P[x_1(t) \le \delta] \le \alpha\delta^\beta.$$

The host species that supports the highest mean parasitoid density excludes all others: apparent competition through a shared natural enemy obeys a $P^*$ rule even in a fluctuating environment.

## Expansion

At a stationary distribution supporting host $1$ and the parasitoid, the mean parasitoid density is $P_1^*$. Host $i$ invading that state has long-run log growth rate $\mathbb{E}[\ln R_i] - \mathbb{E}[a_i] P_1^* = \mathbb{E}[a_i]\,(P_i^* - P_1^*) < 0$, because the parasitoid density process is independent of the current attack rate $a_i(t)$. All other hosts therefore have negative invasion rates at host $1$'s stationary states, while host $1$ can always invade, and the exclusion criterion of Benaïm and Schreiber (accessibility of the face where only host $1$ is present, together with persistence on that face) yields exponential extinction of the inferior hosts. Variance matters only through $\mathbb{E}[\ln R_i]$: a host with more variable fecundity has a lower $P_i^*$ and loses.

## Depends on

- [Stochastic persistence of a host in the Holt–Lawton parasitoid model](stochastic-persistence-of-a-host-in-the-holt-lawton-parasitoid-model.md)

## Sources

- S. J. Schreiber, "The $P^*$ rule in the stochastic Holt–Lawton model of apparent competition", arXiv:2007.01953 (2020), Theorem 3.2, Theorem 4.2 and Section 6 (proof of Theorem 3.2), <https://doi.org/10.48550/arXiv.2007.01953>.
