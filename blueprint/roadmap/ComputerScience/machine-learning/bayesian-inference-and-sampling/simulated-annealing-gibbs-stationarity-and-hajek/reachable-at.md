# Reachability at a height

Let $S$ be a finite state space with a proposal kernel $R$ (for each state $s$, a probability mass function $R(s, \cdot)$ on $S$) and an energy $V : S \to \mathbb{R}$. For a height $E \in \mathbb{R}$, a state $i$ is reachable from a state $j$ at height $E$ when $V(j) \le E$ and $i$ can be reached from $j$ by a finite (possibly empty) path of proposal arcs $a \to b$ with $R(a, b) \ne 0$, every visited state $b$ satisfying $V(b) \le E$. Both endpoints thus have energy at most $E$.
