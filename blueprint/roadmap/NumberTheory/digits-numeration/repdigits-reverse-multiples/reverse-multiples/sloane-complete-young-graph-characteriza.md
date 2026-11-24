# Characterization of complete Young graphs

Let $g$, $k$ and $m$ be natural numbers with
$2 \le k < g$ and $m \ge 2$. Then the Young graph $Y(g, k)$ is complete on $m$ nodes if and only
if

$$
\left\lfloor \frac{\gcd(g - k,\, k^2 - 1)}{k + 1} \right\rfloor = m - 1.
$$

The hypothesis $m \ge 2$ cannot be relaxed to $m \ge 1$: no Young graph is complete on one node,
since the starting node always has an edge to some node other than $[0, 0]$, yet
$(g, k) = (10, 9)$ gives $\lfloor \gcd(1, 80)/10 \rfloor = 0$.

## Sources

- L. H. Kendrick, *Young Graphs: 1089 et al.*, Journal of Integer Sequences 18 (2015), Article 15.9.7, Corollary 32, <https://cs.uwaterloo.ca/journals/JIS/VOL18/Kendrick/ken1.tex>.
