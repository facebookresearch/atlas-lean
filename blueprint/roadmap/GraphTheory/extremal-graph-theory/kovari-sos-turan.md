# Kővári–Sós–Turán bound

Let $m, n, s, t$ be natural numbers with $s \ge 1$ and
$1 \le t \le n$. Let $z(m, n; s, t)$ be the Zarankiewicz number, the largest number of edges in a
bipartite graph with parts of sizes $m$ and $n$ that contains no copy of the complete bipartite
graph $K_{s,t}$. Then

$$z(m, n; s, t) \le (s - 1)^{1/t} (n - t + 1) m^{1 - 1/t} + (t - 1) m.$$

Proof: Double-count common right neighborhoods, apply the power-mean inequality, and take a real
$t$-th root, following Kővári–Sós–Turán (1954) and Jukna, Theorem 2.10.

## Sources

- statement `kovari-sos-turan-s1` from https://en.wikipedia.org/wiki/Zarankiewicz_problem.
