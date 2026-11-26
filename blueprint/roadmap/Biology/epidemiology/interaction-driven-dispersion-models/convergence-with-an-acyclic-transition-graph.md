# Convergence of interaction-driven dispersion models with acyclic transitions

**Model.** A population is split into states $1, \dots, N$ with fractions $y_i(t) \in (0,1)$, $\sum_i y_i(t) = 1$, under uniform mixing. For $k \ne i$, $\beta^k_{im} \ge 0$ is the rate at which an encounter of a state-$i$ agent with a state-$m$ agent moves the former to state $k$, and $\beta^i_{im} = \sum_{k \ne i} \beta^k_{im}$. With outflow and inflow

$$O_i = y_i \sum_{m} \beta^i_{im}\, y_m, \qquad I_i = \sum_{n \ne i}\sum_{k} \beta^i_{nk}\, y_n y_k,$$

the **interaction-driven dispersion model** is $\dot y_i = I_i - O_i$, $i = 1, \dots, N$. The SIR model (recovery written as an encounter with any agent, using $\sum_m y_m = 1$) and the Daley–Kendall rumor model are special cases. The **transition graph** has an arc $u \to v$ ($u \ne v$) whenever $\beta^v_{uk} > 0$ for some $k$.

**Statement.** Suppose $y_i(0) \in (0,1)$ with $\sum_i y_i(0) = 1$. Then $0 < y_i(t) < 1$ for all $t \ge 0$, and $I_i(t) \le \sum_{k \in \mathscr P_i} O_k(t)$, where $\mathscr P_i$ is the set of transition predecessors of $i$. If the transition graph is a directed acyclic graph, then for every state

$$\lim_{t\to\infty} y_i(t) = y_i^\ast \in [0,1], \qquad \lim_{t \to\infty} \dot y_i(t) = 0, \qquad \lim_{t\to\infty} O_i(t) = \lim_{t\to\infty} I_i(t) = 0,$$

and $\int_0^\infty I_i\,dt$ and $\int_0^\infty O_i\,dt$ are finite.

## Depends on

- [Kermack–McKendrick SIR model](../kermack-mckendrick-sir-model/README.md)

## Expansion

A DAG has a source, which receives no inflow, so its fraction is nonincreasing and converges, and its total outflow $\int_0^\infty O\,dt \le y(0)$ is finite. Inducting along a topological order, the inflow of each state is bounded by the outflows of its predecessors, which are integrable by the induction hypothesis; hence $y_i(t) - \int_0^t I_i$ is nonincreasing and bounded, so $y_i$ converges and $\int_0^\infty O_i < \infty$. Uniform continuity of $I_i$ and $O_i$ (the right-hand side is a polynomial in bounded variables) turns integrability into convergence to zero.

## Sources

- K. M. D. Chan, D. T. Crommelin and M. R. H. Mandjes, Asymptotic behavior for a general class of spreading models, arXiv (2025). <https://doi.org/10.48550/arXiv.2511.02437> (Theorem 1, Lemmas 2, 3 and 4, Assumption 1, Definition 6.)
