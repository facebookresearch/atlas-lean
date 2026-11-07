# Young's theorem on reverse multiples

Let $g$ and $k$ be natural numbers with $2 \le k < g$.
A $(g, k)$ reverse multiple is a list of base-$g$ digits $d_1, d_2, \dots, d_n$, most significant
first, with $n \ge 2$, $d_1 \ne 0$, $d_n \ne 0$ and $d_i < g$ for every $i$, such that $k$ times
the number $\sum_{i=1}^{n} d_i g^{n-i}$ equals the number $\sum_{i=1}^{n} d_{n+1-i} g^{n-i}$
whose digits are those of the first in reverse order. Consider the graph whose nodes are pairs
$(r, s)$ of natural numbers, with an edge labeled $(a, b)$ from $(r, s)$ to $(r', s')$ whenever
$k b + s = a + s' g$ and $k a + r' = b + r g$. A path is a sequence of nodes $v_0, \dots, v_m$
together with a sequence of labels $\ell_1, \dots, \ell_m$ such that $m \ge 1$, $v_0 = (0, 0)$,
both coordinates of every node are less than $k$, both coordinates of every label are less
than $g$, both coordinates of $\ell_1$ are nonzero, and for each $j$ the label $\ell_j$ labels an
edge from $v_{j-1}$ to $v_j$. A node $(r, s)$ is an even pivot if $r = s$, and an odd pivot if
for some $c < g$ there is an edge labeled $(c, c)$ from $(r, s)$ to $(s, r)$.

Then there is a bijection from the $(g, k)$ reverse multiples with an even number of digits to
the paths whose last node is an even pivot, and a bijection from the $(g, k)$ reverse multiples
with an odd number of digits to the paths whose last node is an odd pivot. Under both
bijections, a reverse multiple $d_1, \dots, d_n$ is sent to a path with labels
$(d_1, d_n), (d_2, d_{n-1}), \dots, (d_h, d_{n+1-h})$, where $h = \lfloor n/2 \rfloor$; in the
odd case, if $(r, s)$ is the last node of that path, there is an edge labeled
$(d_{h+1}, d_{h+1})$ from $(r, s)$ to $(s, r)$.

## Sources

- L. H. Kendrick, *Young Graphs: 1089 et al.*, Journal of Integer Sequences 18 (2015), Article 15.9.7, Theorem [Young's Theorem], lines 192-197, <https://cs.uwaterloo.ca/journals/JIS/VOL18/Kendrick/ken1.tex>, after Theorems 1 and 2 of Young's first paper on reverse multiples.
