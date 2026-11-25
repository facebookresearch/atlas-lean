# Long clusters do not force giant components

Call a finite graph a $(b, d)$-expander if all degrees are at most $d$ and every set $S$ of at most half the vertices has at least $b|S|$ edges leaving it. In bond percolation with $p = 1/2$, the diameter of a cluster is measured in the cluster itself. The claim fails: there are $b > 0$, $d$, $(b, d)$-expanders $G_k$ with $|V(G_k)| \to \infty$ and vertices $v_k$ whose cluster has diameter greater than $\mathrm{diam}(G_k)/2$ with probability greater than $1/2$ for every $k$, such that for no $c > 0$ does the probability that some cluster has at least $c|V(G_k)|$ vertices tend to $1$ (Krivelevich, Lubetzky and Sudakov).

## Sources

- Problem: I. Benjamini, Coarse Geometry and Randomness (Saint-Flour lecture notes 2011; Lecture Notes in Mathematics 2100, Springer 2013), Open problem 11.7, PDF p. 86.
- Resolution: M. Krivelevich, E. Lubetzky and B. Sudakov, Asymptotics in percolation on high-girth expanders, Random Structures Algorithms 56 (2020), 927-947; arXiv:1803.11553, https://arxiv.org/abs/1803.11553.
