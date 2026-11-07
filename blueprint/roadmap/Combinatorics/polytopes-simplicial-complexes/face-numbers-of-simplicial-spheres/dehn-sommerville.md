# Dehn–Sommerville equations

Let $X$ be a finite simplicial $(d-1)$-sphere, that is, a
finite geometric simplicial complex in $\mathbb{R}^d$ whose underlying space is homeomorphic to
the unit sphere of $\mathbb{R}^d$. Then for every natural number $j \le d$, the h-vector of $X$
satisfies $h_j = h_{d-j}$. Here $h_j = \sum_{i=0}^{j} (-1)^{j-i} \binom{d-i}{j-i} f_{i-1}$,
where $f_{-1} = 1$ and $f_k$ is the number of $k$-dimensional faces of $X$.

## Sources

- M. Dehn (1905); D. M. Y. Sommerville (1927); see Stanley, *Combinatorics and Commutative Algebra*. Knill, *Some fundamental theorems in mathematics*, §142. Problem `dehn_sommerville` of the lean-eval benchmark.
