# Edge hitting times and Kac's formula for the simple random walk on a connected graph

Let $G = (V, E)$ be a finite connected simple graph and consider the simple random walk (move to a uniformly random neighbour). Let $\tau_v$ be the first time $\ge 0$ the walk visits $v$, $\tau_v^+$ the first time $\ge 1$, and $\mathbb{E}_u$ the expectation from start $u$, valued in $[0, \infty]$. Then

(1) (Kac) for every vertex $v$, $\deg(v)\, \mathbb{E}_v[\tau_v^+] = 2|E|$;

(2) for every edge $\{u, v\}$, $\mathbb{E}_u[\tau_v] + \deg(v) \le 2|E|$, so $\mathbb{E}_u[\tau_v] \le 2|E|$;

(3) for all $u, v$, $\mathbb{E}_u[\tau_v] \le \operatorname{dist}(u, v)\cdot 2|E|$.

## Proof sketch

The degree measure $\pi(x) = \deg(x)/2|E|$ is stationary, and Kac's lemma gives $\mathbb{E}_v[\tau_v^+] = 1/\pi(v)$. Decomposing the return to $v$ by the first step, $\deg(v)\mathbb{E}_v[\tau_v^+] = \sum_{w \sim v}(1 + \mathbb{E}_w[\tau_v])$, and keeping only the term $w = u$ gives (2). Summing (2) along a shortest path gives (3).

## Depends on

- [First-step equations for hitting times](../part-01/effective-resistance-and-electrical-networks/is-hitting-time-solution.md)

## Sources

- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
