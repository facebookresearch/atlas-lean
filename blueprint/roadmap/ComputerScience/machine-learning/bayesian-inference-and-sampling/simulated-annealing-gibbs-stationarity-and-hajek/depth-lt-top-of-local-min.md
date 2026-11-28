# Local minima have finite depth under strong irreducibility

Let $S$ be a finite state space with a proposal kernel $R$ (for each state $s$, a probability mass function $R(s, \cdot)$ on $S$) and an energy $V : S \to \mathbb{R}$. A state $i$ is reachable from $j$ at height $E$ when $V(j) \le E$ and there is a path $j = a_0, a_1, \dots, a_r = i$ ($r \ge 0$) with $R(a_{l}, a_{l+1}) \ne 0$ and $V(a_{l+1}) \le E$ for every step. The depth of a state $s$ is the infimum, in $[0, \infty]$, of the heights $E > 0$ such that some state $t$ with $V(t) < V(s)$ is reachable from $s$ at height $V(s) + E$; it is $\infty$ when no such $E$ exists. Assume strong irreducibility: for all states $i, j$ there is a height $E$ at which $i$ is reachable from $j$.

Let $s$ be a local minimum in Hajek's sense (no state $t$ with $V(t) < V(s)$ is reachable from $s$ at height $V(s)$) that is not a global minimum. Then the depth of $s$ is finite:

$$\mathrm{depth}(s) < \infty .$$

## Sources

B. Hajek, *Optimization by simulated annealing: a necessary and sufficient condition for convergence*, in Adaptive Statistical Procedures and Related Topics, IMS Lecture Notes–Monograph Series 8 (1986), 417–427.
