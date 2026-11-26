# Size function of a piecewise-constant history

For a [piecewise-constant history](piecewise-history.md) with $K$ pieces, sizes $\nu_j$ and start times $s_j$, the size function at a real time $s$ is

$$\eta(s) = \sum_{j=0}^{K-1} \nu_j\, \mathbf{1}\bigl[s_j \le s \text{ and } (j + 1 < K \Rightarrow s < s_{j+1})\bigr]:$$

for $s \ge 0$ and $K \ge 1$ it is the size of the piece $j$ with $s_j \le s < s_{j+1}$ (the last piece has no end), and it is $0$ for $s < 0$.
