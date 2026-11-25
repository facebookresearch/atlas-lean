# Compact containment and C-tightness for rescaled critical binary branching

Fix $\gamma>0$ and $x\ge0$. For $N\ge1$ let $Z^N$ be the [linear birth–death process](prob.md) in which each individual gives birth at rate $\gamma N/2$ and dies at rate $\gamma N/2$, started from $Z^N_0=\lfloor Nx\rfloor$, and put $M^N_t=Z^N_t/N$. Then:

1. $M^N$ is a martingale with jumps of size $1/N$ and predictable quadratic variation

$$\langle M^N\rangle_t=\gamma\int_0^tM^N_s\,ds,$$

obtained from [the predictable quadratic variation of Dynkin martingales](../../martingales/stopping-times-and-martingale-problems/predictable-quadratic-variation-of-dynkin-martin.md) for the chain stopped on leaving $\{Z\le KN\}$, followed by localization $K\to\infty$.

2. $\mathbb E(M^N_t)^2=(\lfloor Nx\rfloor/N)^2+\gamma(\lfloor Nx\rfloor/N)\,t$ exactly, and for every $T>0$, uniformly in $N$,

$$\mathbb E\sup_{t\le T}(M^N_t)^2\le4\,(x^2+\gamma xT).$$

3. For every $T>0$ there is $C=C(x,\gamma,T)$ such that for all $N$, all stopping times $\tau\le T$ and all $0<\delta\le1$,

$$\mathbb E\bigl|M^N_{\tau+\delta}-M^N_\tau\bigr|^2=\gamma\,\mathbb E\int_\tau^{\tau+\delta}M^N_s\,ds\le\gamma\,\delta\,\mathbb E\sup_{s\le T+1}M^N_s\le C\,\delta .$$

Consequently the laws of $(M^N)_{N\ge1}$ satisfy compact containment in $[0,\infty)$ and are C-tight in $D([0,T],[0,\infty))$, by the [Aldous tightness criterion with initial and compact-containment conditions](../../convergence-of-measures/skorokhod-space/aldous-tightness-criterion-in-d-0-t-e-with-initi.md): the initial values are deterministic and converge, compact containment follows from item 2 and Markov's inequality, Aldous's condition from item 3, and the maximal jump is $1/N\to0$. Discrete-generation critical Galton–Watson processes with general offspring laws are a separate statement; they need third-moment or Lindeberg control of the jumps.

## Depends on

- [Kendall's law of the linear birth–death process](prob.md)
- [Predictable quadratic variation of Dynkin martingales for bounded-generator jump processes](../../martingales/stopping-times-and-martingale-problems/predictable-quadratic-variation-of-dynkin-martin.md)
- [Aldous tightness criterion in D([0,T],E) with initial and compact-containment conditions](../../convergence-of-measures/skorokhod-space/aldous-tightness-criterion-in-d-0-t-e-with-initi.md)

## Proof depends on

- [Non-explosion criteria and Kolmogorov equations (countable state)](../../markov-chains/finite-continuous-time-markov-chains/finite-continuous-time-markov-chains-as-path-pro/non-explosion-criteria-and-kolmogorov-equations.md)
- [Optional stopping for right-continuous martingales](../../martingales/stopping-times-and-martingale-problems/optional-stopping-right-continuous.md)
- [Doob's $L^2$ maximal inequality for right-continuous martingales](../../martingales/stopping-times-and-martingale-problems/doob-l2-maximal-inequality-right-continuous.md)

## Expansion

A full proof computes the generator of $M^N$: jumps $\pm1/N$, each at total rate $\gamma N^2M/2$, so the drift vanishes and the jump variance rate is $\gamma M$. It should establish the exact second moment from $\mathbb E(M^N_t)^2=\mathbb E(M^N_0)^2+\gamma\int_0^t\mathbb E M^N_s\,ds$, the maximal bound from Doob's $L^2$ inequality, and the increment bound from optional stopping for the martingale $(M^N)^2-\langle M^N\rangle$. Optional stopping and Doob's $L^2$ maximal inequality are needed for right-continuous martingales, not only continuous ones. The containment bound alone is not C-tightness: the increment estimate and the vanishing jump size are separate steps.

## Sources

- S. N. Ethier and T. G. Kurtz, *Markov Processes: Characterization and Convergence*, Wiley, 1986, <https://doi.org/10.1002/9780470316658>, branching limits and compact containment (topic).
