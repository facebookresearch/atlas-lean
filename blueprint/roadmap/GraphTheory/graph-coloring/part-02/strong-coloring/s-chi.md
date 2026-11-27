# Strong chromatic number

Let $G$ be a simple graph on a finite vertex set $V$. The strong chromatic number $\chi_s(G)$ is the least **positive** integer $k$ such that $G$ is [strongly $k$-colorable](is-strongly-colorable.md): for every partition of $V$ into nonempty parts of size at most $k$ there is a proper coloring of $G$ with colors $\{0, \dots, k-1\}$ that is injective on each part. Such a $k$ exists: for $V$ nonempty, $k = |V|$ works, using a coloring that is injective on all of $V$. For $V$ empty, every positive $k$ works, so by this convention $\chi_s(G) = 1$.

The restriction to positive $k$ is essential. For $k = 0$ no partition of a nonempty set into nonempty parts has all parts of size at most $0$, so every graph is strongly $0$-colorable vacuously, and an infimum over all natural numbers would be $0$ for every graph.

## Sources

- Wikipedia, *Strong coloring*, https://en.wikipedia.org/wiki/Strong_coloring
