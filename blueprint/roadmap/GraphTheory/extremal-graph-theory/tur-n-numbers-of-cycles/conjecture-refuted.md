# Erdős Problem 574 is false

It is not the case that for every natural number $k \ge 2$ the
ratio $\mathrm{ex}(n; \{C_{2k-1}, C_{2k}\}) / (n/2)^{1 + 1/k}$ tends to $1$ as $n \to \infty$.
Here $\mathrm{ex}(n; \{C_{2k-1}, C_{2k}\})$ is the extremal number: the supremum of the numbers
of edges of simple graphs on $n$ vertices that contain no copy of the cycle graph $C_{2k-1}$ and
no copy of the cycle graph $C_{2k}$.

At $k=3$, doubling each line of the Wenger graph gives $2q^4$ edges on $n=3q^3$ vertices
for $q=2^{m+1}$, with no copy of $C_5$ or $C_6$. This applies the one-sided blow-up of Lazebnik,
Ustimenko and Woldar and realizes the bipartite lower bound $(2/3^{4/3})n^{4/3}$ of Füredi,
Naor and Verstraëte (*On the Turán number for the hexagon*, Adv. Math. 203 (2006), 476–496).

Lazebnik, Ustimenko and Woldar (Discrete Math. 1999), per Füredi–Simonovits
(arXiv:1306.5167, Construction 4.28), blow up one side of Benson's girth-12 bipartite graph to
get bipartite $C_{10}$-free graphs (hence also $C_9$-free) with
$4(n/5)^{6/5} > 0.5798\, n^{6/5}$ edges for infinitely many $n$, refuting the case $k = 5$.

## Sources

- Zoltán Füredi and Miklós Simonovits, The history of degenerate (bipartite) extremal graph problems, in Erdős Centennial, Bolyai Soc. Math. Stud. 25 (2013), arXiv:1306.5167, https://arxiv.org/abs/1306.5167.
