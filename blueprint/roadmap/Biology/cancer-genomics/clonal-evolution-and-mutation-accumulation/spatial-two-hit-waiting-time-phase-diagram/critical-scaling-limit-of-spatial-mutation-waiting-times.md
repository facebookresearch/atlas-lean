# Critical scaling limit of spatial mutation waiting times

**Model.** On the $d$-dimensional torus of volume $N$, type-$(i-1)$ points acquire an $i$-th mutation as a space–time Poisson process of rate $\mu_i$ per unit volume, and every mutation spreads as a ball of radius growing at speed $\alpha$, overtaking points of lower type. Let $\sigma_k$ be the first time some point has type $k$. For $c_1, \dots, c_k > 0$, let $Z_{d,k}(c_1, \dots, c_k)$ denote the same waiting time for the process on the unit torus $[0,1]^d$ with speed $1$ and rates $c_1, \dots, c_k$; let $\gamma_d$ be the volume of the unit ball.

**Theorem (critical regime).** Fix $k \ge 2$. If $\mu_iN^{(d+1)/d}/\alpha \to c_i \in (0,\infty)$ for every $i \le k$, then

$$\frac{\alpha\,\sigma_k}{N^{1/d}} \Rightarrow Z_{d,k}(c_1, \dots, c_k).$$

For $k = 2$, if $\mu_1N^{(d+1)/d}/\alpha \to c_1$ and $\mu_2\alpha^d/(N\mu_1)^{d+1} \to c_2$, then $\alpha\sigma_2/N^{1/d} \Rightarrow Z_{d,2}(c_1, c_2c_1^{d+1})$. In this regime the arrival of a mutation, its spread over a macroscopic fraction of the space, and the next arrival all occur on the same time scale, so the limit is a nondegenerate law that depends on the full geometry of overlapping balls.

**Proposition (bounds on the limit law).** With $W_1, \dots, W_k$ independent and $W_i \sim \mathrm{Exp}(c_i)$,

$$\sum_{i=1}^kW_i \preceq Z_{d,k}(c_1, \dots, c_k) \preceq \frac{(k-1)\sqrt{d}}{2} + \sum_{i=1}^kW_i$$

in the stochastic order.

**Proposition (small-time behavior).** For all $d, k \ge 1$ and $c_1, \dots, c_k > 0$,

$$\lim_{t \to 0}t^{-((k-1)d+k)}\,\mathbb{P}\big(Z_{d,k}(c_1, \dots, c_k) \le t\big) = \frac{(d!)^{k-1}\gamma_d^{k-1}c_1\cdots c_k}{((k-1)d+k)!}.$$

## Expansion

The scaling limit is exact rescaling: shrinking space by $N^{1/d}$ and time by $N^{1/d}/\alpha$ makes balls grow at unit speed and turns the mutation rates into $\mu_iN^{(d+1)/d}/\alpha$; continuity of the law of $Z_{d,k}$ in the rates finishes the proof. The lower bound comes from letting each new type instantly cover the torus, the upper bound from suppressing further mutations until each sweep is complete, which takes at most the diameter $\sqrt{d}/2$ of the unit flat torus $\mathbb R^d/\mathbb Z^d$ (balls grow at unit speed). For small $t$, the expected type-$j$ volume satisfies $m_j(t) \le \int_0^tc_jm_{j-1}(u)\gamma_d(t-u)^d\,du$, and iterating with the Beta integral $\int_0^1y^a(1-y)^b\,dy = a!\,b!/(a+b+1)!$ gives the matching upper bound by Markov's inequality; the lower bound keeps only the first mutation of each type, whose successive inter-arrival times have explicit densities for $t < 1/2$. The exponent $(k-1)(d+1)$ of the incidence rate $\frac{d}{dt}\mathbb{P}(Z \le t)$ near $0$ differs from the Armitage–Doll power $t^{k-1}$ of nonspatial multistage carcinogenesis: each intermediate clone contributes $d$ extra powers from its growing volume.

## Sources

- Jasmine Foo, Kevin Leder, Jason Schweinsberg, "Mutation timing in a spatial model of evolution", arXiv:2001.01175 (2020): Section 3 (Case 3 heuristics for $k \ge 3$), Theorem 12 (critical scaling limit), Corollary 13 (two mutations), Propositions 14 and 15 (stochastic bounds and small-time asymptotics of $Z_{d,k}$). <https://doi.org/10.48550/arXiv.2001.01175>
