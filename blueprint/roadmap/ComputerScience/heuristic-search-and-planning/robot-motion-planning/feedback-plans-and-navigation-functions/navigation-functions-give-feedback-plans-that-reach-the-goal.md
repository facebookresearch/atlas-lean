# Navigation functions give feedback plans that reach the goal

Let $X$ be a finite state set, $U(x)$ a finite nonempty set of actions at $x$, $f(x, u)$ the next state, and $X_G \subseteq X$ the goal set. A function $\varphi : X \to [0, \infty]$ is a **navigation function** if

- $\varphi(x) = 0$ for $x \in X_G$;
- $\varphi(x) = \infty$ exactly when no state of $X_G$ is reachable from $x$;
- for every $x \notin X_G$ from which $X_G$ is reachable, some action $u \in U(x)$ gives $\varphi(f(x, u)) < \varphi(x)$.

Let $\pi(x) \in \operatorname{argmin}_{u \in U(x)} \varphi(f(x, u))$ be the greedy feedback plan. Then:

1. **Arrival.** From every state $x$ from which $X_G$ is reachable, following $\pi$ reaches $X_G$ after at most $|X| - 1$ steps, and the values of $\varphi$ strictly decrease until then.
2. **Integer navigation functions.** If $\varphi$ takes values in $\{0, 1, 2, \dots\} \cup \{\infty\}$, at most $\varphi(x)$ steps are needed.
3. **Existence.** The number of steps of a shortest action sequence from $x$ to $X_G$ ($\infty$ if there is none) is a navigation function.

**Proof.** For part 1, along the greedy trajectory $x_{k+1} = f(x_k, \pi(x_k))$, as long as $x_k \notin X_G$ we have $\varphi(x_{k+1}) \le \min_u \varphi(f(x_k, u)) < \varphi(x_k) < \infty$, so $X_G$ remains reachable and the values strictly decrease. Hence no state repeats, and since $X$ is finite the trajectory enters $X_G$ within $|X| - 1$ steps. In part 2, each step lowers $\varphi$ by at least $1$. For part 3, the shortest-path length $d$ is $0$ on $X_G$, infinite exactly when $X_G$ is unreachable, and for reachable $x \notin X_G$ the first action of a shortest sequence leads to a state with $d$ one smaller.

## Sources

- S. M. LaValle, *Planning Algorithms*, Cambridge University Press, 2006, <http://lavalle.pl/planning/>, Section 8.2.2, feedback plans as navigation functions: the local operator (8.4), the definition of a feasible navigation function by its three conditions, and the remark that the cost-to-go of a backward Dijkstra or wavefront computation is a navigation function (pp. 376–377). The step bounds are derived on the page.
