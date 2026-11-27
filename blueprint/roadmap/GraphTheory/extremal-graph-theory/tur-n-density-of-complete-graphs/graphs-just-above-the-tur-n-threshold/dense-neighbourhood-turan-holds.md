# Resolution of Erdős Problem 1079

For every natural number $r \ge 4$ there is a real $c > 0$ such that for every natural number $n \ge 2$, every simple graph $G$ on $\{0, \dots, n-1\}$ with at least $\mathrm{ex}(n; K_r)$ edges has a vertex $v$ of degree $d \ge c\,n$ whose neighbourhood spans at least $\mathrm{ex}(d; K_{r-1})$ edges, counting the edges of the subgraph induced by the neighbours of $v$. Here $\mathrm{ex}(m; K_s)$ is the largest number of edges of a $K_s$-free simple graph on $m$ vertices. That is, the proposition [Erdős Problem 1079 (a vertex with a dense neighbourhood)](dense-neighbourhood-turan.md) holds.

The statement includes the Turán graph $T_{r-1}(n)$, the complete $(r-1)$-partite graph on $n$ vertices with parts as equal as possible, which has exactly $\mathrm{ex}(n; K_r)$ edges; there it holds with equality for every $c \le (r-2)/(r-1)$. A vertex $v$ in a smallest part has degree $d = n - \lfloor n/(r-1) \rfloor \ge \frac{r-2}{r-1}\, n$, and its neighbourhood, the union of the other $r - 2$ parts, induces the balanced complete $(r-2)$-partite graph $T_{r-2}(d)$, which has exactly $\mathrm{ex}(d; K_{r-1})$ edges by Turán's theorem.

## Sources

- T. F. Bloom, Erdős Problems, Problem #1079, https://www.erdosproblems.com/1079.
- B. Bollobás and A. Thomason, Dense neighbourhoods and Turán's theorem, J. Combin. Theory Ser. B 31 (1981), 111–114.
- J. A. Bondy, Large dense neighbourhoods and Turán's theorem, J. Combin. Theory Ser. B 34 (1983), 109–111, https://doi.org/10.1016/0095-8956(83)90012-6.
- P. Turán, Egy gráfelméleti szélsőértékfeladatról (On an extremal problem in graph theory), Mat. Fiz. Lapok 48 (1941), 436–452 (Turán's theorem, for the equality case on $T_{r-1}(n)$).
