# Lotka–Euler equation for SIR epidemics on configuration networks

Let a large population form a configuration-model network with degree distribution $D$ of finite mean and variance, so that the early epidemic is locally tree-like. An infected individual draws an i.i.d. random **infectivity profile** $\Lambda(t)$, $t \ge 0$ the time since infection, and makes infectious contacts with *each* neighbour at the points of an inhomogeneous Poisson process of rate $\Lambda(t)$; only the first contact along an edge can transmit. Let $A = \int_0^\infty \Lambda(t)\,dt$ (with $\mathbb E[A] < \infty$) and $\kappa = \mathbb E[D(D-1)]/\mathbb E[D]$, the mean excess degree of a node reached along an edge. The rate of first contacts along an edge is

$$\Lambda_1(t) = \Lambda(t)\,e^{-\int_0^t \Lambda(s)\,ds}, \qquad \int_0^\infty \Lambda_1 = 1 - e^{-A}.$$

**Basic reproduction number.**

$$R_0 = \kappa\,\mathbb E\big[1 - e^{-A}\big].$$

**Real-time growth rate.** The mean infection intensity of a typical early infective is $\beta(t) = \kappa\,\mathbb E[\Lambda_1(t)]$, and the early exponential growth rate $r$ of incidence is the unique real solution of

$$\int_0^\infty \beta(t)\,e^{-rt}\,dt = 1, \qquad\text{equivalently}\qquad \int_0^\infty w_1(t)\,e^{-rt}\,dt = \frac{1}{R_0},$$

where $w_1(t) = \mathbb E[\Lambda_1(t)]/\mathbb E[1 - e^{-A}]$ is the **generation-interval** density, distinct from the **contact-interval** density $w(t) = \mathbb E[\Lambda(t)]/\mathbb E[A]$. Thus $r < 0$, $r = 0$, $r > 0$ according as $R_0 < 1$, $= 1$, $> 1$.

**Proposition (generation versus contact intervals).** Let $W, W_1$ have densities $w, w_1$ and let $M$ be the number of contacts along an edge. Then

$$\mathbb P(W_1 \le x \mid M > 0) = 1 - \frac{\mathbb E_\Lambda\big[e^{-A\,\mathbb P(W \le x \mid M>0, \Lambda)} - e^{-A}\big]}{\mathbb E_\Lambda\big[1 - e^{-A}\big]}.$$

If $A$ is exponentially distributed, then $M \sim \mathrm{Geom}(p)$ with $p = 1/(\mathbb E[A] + 1)$, and

$$\mathbb P(W_1 \le x) = 1 - \frac{p\,\mathbb P(W > x)}{1 - (1-p)\,\mathbb P(W > x)},$$

so the generation interval is stochastically shorter than the contact interval.

Because only first contacts transmit, a network epidemic both infects fewer neighbours than a homogeneously mixing epidemic of equal total infection pressure ($\kappa\mathbb E[A] = R_0^h$) and makes its infections earlier in the infectious period; approximating $w_1$ by $w$ in the Lotka–Euler equation therefore misestimates $r$.

## Expansion

An individual reached along an edge has degree $d$ with probability $d\,\mathbb P(D=d)/\mathbb E[D]$ and $d - 1$ susceptible neighbours; given its profile, each is infected independently with probability $1 - e^{-A}$, the probability of at least one Poisson contact. Averaging gives $R_0$. The time of infection of a given neighbour is the time of the first point of the Poisson process, whose intensity is $\Lambda_1$; summing over the excess degree gives $\beta$. The expected incidence satisfies the renewal equation $i(\tau) = \int_0^\infty \beta(t)\,i(\tau - t)\,dt$, and the exponential ansatz yields the Lotka–Euler equation, whose left side is strictly decreasing in $r$, giving uniqueness. The distributional identity follows by conditioning on $\Lambda$: given $\Lambda$, contacts by time $x$ form a Poisson number with mean $A\,\mathbb P(W \le x \mid \Lambda)$, so the first contact occurs by $x$ with probability $1 - e^{-A\mathbb P(W\le x\mid\Lambda)}$.

## Sources

- Lorenzo Pellis, Simon E. F. Spencer, Thomas House, "Real-time growth rate for general stochastic SIR epidemics on unclustered networks", arXiv (2015). Section 2 (configuration network model, infectivity profile, $R_0$, real-time growth rate and Lotka–Euler equation, homogeneously mixing comparison and approximation), Propositions 1–4. <https://doi.org/10.48550/arXiv.1501.04824>. Published version: Mathematical Biosciences 265 (2015), 65–81, <https://doi.org/10.1016/j.mbs.2015.04.006>; locators above refer to the arXiv version.
