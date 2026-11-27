# The front-door adjustment

**The front-door adjustment** (Pearl 1995; Pearl 2009, Theorem 3.3.4): let $B$ be a Bayesian
network on the nodes $0, \dots, n - 1$ with values in a finite nonempty type $\alpha$ and joint
distribution $P$, and let $P_{\mathrm{do}(X_k = a)}$ be the joint distribution of the
[intervention](intervene.md) $\mathrm{do}(X_k = a)$. Let $k \ne y$ be a treatment node and an
outcome node and $M$ a finite set of nodes with $k, y \notin M$ such that

- every directed path from $k$ to $y$ meets $M$;
- every path from $k$ to a node of $M$ that begins with an arrow into $k$ is blocked by $\emptyset$;
- every path from a node $m \in M$ to $y$ that begins with an arrow into $m$ is blocked by $\{k\}$;
- $P(X_k = a', X_M = m) \ne 0$ for all $a' \in \alpha$ and $m \in \alpha^M$.

Then for every $v \in \alpha$,

$$P_{\mathrm{do}(X_k = a)}(X_y = v) = \sum_{m \in \alpha^M} \frac{P(X_k = a, X_M = m)}{P(X_k = a)} \sum_{a' \in \alpha} \frac{P(X_k = a', X_y = v, X_M = m)}{P(X_k = a', X_M = m)} \, P(X_k = a'),$$

where $P(E)$ is the sum of $P(x)$ over the configurations $x \in \alpha^n$ in $E$.
