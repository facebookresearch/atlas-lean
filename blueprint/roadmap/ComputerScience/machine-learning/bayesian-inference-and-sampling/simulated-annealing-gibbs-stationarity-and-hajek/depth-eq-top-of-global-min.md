# Global minima have infinite depth

Let $S$ be a finite state space with a proposal kernel $R$ (for each state $s$, a probability mass function $R(s, \cdot)$ on $S$) and an energy $V : S \to \mathbb{R}$. The depth of a state $s$ is the infimum, in $[0, \infty]$, of the heights $E > 0$ such that some state $t$ with $V(t) < V(s)$ is reachable from $s$ at height $V(s) + E$; it is $\infty$ when no such $E$ exists.

Every global minimum $s \in S^\ast$ (that is, $V(s) \le V(t)$ for all $t$) has depth $\infty$, since no state has strictly lower energy.

## Sources

B. Hajek, *Optimization by simulated annealing: a necessary and sufficient condition for convergence*, in Adaptive Statistical Procedures and Related Topics, IMS Lecture Notes–Monograph Series 8 (1986), 417–427.
