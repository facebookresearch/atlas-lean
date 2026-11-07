# Characterization of complete Young graphs

Let $g$, $k$ and $m$ be natural numbers with
$2 \le k < g$ and $m \ge 2$. Then the Young graph $Y(g, k)$ is complete on $m$ nodes if and only
if

$$\left\lfloor \frac{\gcd(g - k,\, k^2 - 1)}{k + 1} \right\rfloor = m - 1.$$

## Sources

- Corollary at lines 574-576 of L. H. Kendrick, "Young Graphs: 1089 et al.", Journal of Integer Sequences 18 (2015), <https://cs.uwaterloo.ca/journals/JIS/VOL18/Kendrick/ken1.tex>. In the source's `K_m` convention, the nodes other than the distinguished starting node form the complete directed graph on `m` nodes, so the Young graph has `m + 1` total nodes including that distinguished start; `[0, 0]` is one of the `m` non-start nodes. Natural-number division represents the source floor because all quantities are nonnegative and the denominator is positive. The hypothesis is `2 ≤ m`, not `1 ≤ m`. The corollary rests on a theorem whose proof starts "Since $s_1$ exists", so it needs `m - 1 ≥ 1`. For `m = 1` the class `K_1` contains no Young graph: every Young graph is connected and contains `[0, 0]`, so the starting node has an edge to some node other than `[0, 0]`, while a graph in `K_1` has none. With `1 ≤ m`, `(g, k) = (10, 9)` and `m = 1` give `gcd(1, 80) / 10 = 0 = m - 1`, but `Y(10, 9)` is the 1089 graph, not in `K_1`.
