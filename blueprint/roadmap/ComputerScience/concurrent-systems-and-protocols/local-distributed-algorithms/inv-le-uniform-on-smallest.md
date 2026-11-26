# Key estimate of Luby's analysis

Let $G$ be a graph on $\{0, \dots, n-1\}$, let $R$ be a
set of vertices, write $N_R(w)$ for the set of neighbors of a vertex $w$ in $R$ and
$d_R(w) = |N_R(w)|$, and let $uv$ be an edge of $G$ with $u \in R$. For a uniformly random
permutation $\sigma$ of the vertices, the probability that $\sigma(u) < \sigma(w)$ for every
$w \in N_R(u) \cup N_R(v)$ other than $u$, that is, that $u$ has the smallest value in
$N_R(u) \cup N_R(v)$, is at least $1/(d_R(u) + d_R(v))$.

The uniform measure on the permutations is taken for any measurable structure on them in which
singletons are measurable; it does not depend on that structure.
