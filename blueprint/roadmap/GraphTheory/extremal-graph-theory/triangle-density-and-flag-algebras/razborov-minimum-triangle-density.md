# Razborov's minimum triangle density theorem

For every edge density $a \in [0, 1]$ and every $\varepsilon > 0$ there is $N$ such that every simple graph on $n \ge N$ vertices with at least $a\binom{n}{2}$ edges has at least $(h(a) - \varepsilon)\binom{n}{3}$ triangles, where $h$ is [Razborov's triangle density function](razborov-triangle-density.md).

Equivalently, $g_3(a) \ge h(a)$ for the limit $g_3(a) = \lim_n g_3(\lfloor a\binom{n}{2}\rfloor, n)/\binom{n}{3}$, where $g_3(m, n)$ is the least number of triangles in a graph with $n$ vertices and $m$ edges; the $\varepsilon$–$N$ form follows because $g_3(m, n)$ does not decrease when $m$ grows. Together with the complete multipartite constructions behind $h$, this determines $g_3(a) = h(a)$, answering the question of Erdős (1955) in the form conjectured by Lovász and Simonovits. Razborov's proof was one of the first major applications of flag algebras. Nikiforov (2011) did the same for $K_4$, and Reiher (2016) for every $K_r$.

## Background

- [Goodman's bound on the number of triangles](goodman.md): the earlier bound $g_3(a) \ge a(2a - 1)$, tight only at $a = 1 - 1/t$.

## Sources

- A. A. Razborov, On the minimal density of triangles in graphs, Combin. Probab. Comput. 17 (2008), 603-618.
- O. Pikhurko and A. Razborov, Asymptotic structure of graphs with the minimum number of triangles, Combin. Probab. Comput. 26 (2017), arXiv:1204.2846v2, introduction: equations (1)-(4) and the paragraph after (4).
