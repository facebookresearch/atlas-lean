# Schmidt's subspace theorem

Let $\sigma$ be a finite set with at least two elements, and
for $i \in \sigma$ let $L_i(x) = \sum_{j \in \sigma} a_{ij} x_j$ be linear forms whose
coefficients $a_{ij} \in \mathbb{C}$ are algebraic over $\mathbb{Q}$ and whose coefficient
vectors $(a_{ij})_{j \in \sigma}$ are linearly independent over $\mathbb{C}$. Let
$\varepsilon > 0$ be real. Then there is a finite set $S$ of nonzero vectors in
$\mathbb{Z}^\sigma$ such that every $x \in \mathbb{Z}^\sigma$ with
$\left|\prod_{i \in \sigma} L_i(x)\right| < \|x\|^{-\varepsilon}$, where
$\|x\| = \max_{j \in \sigma} |x_j|$, satisfies $\sum_{i \in \sigma} c_i x_i = 0$ for some $c \in S$.

Every proper subspace of $\mathbb{Q}^\sigma$ lies in a hyperplane $\sum_i c_i x_i = 0$ with a
nonzero integer vector $c$, so this is the usual form: these $x$ lie in finitely many proper
subspaces.

## Sources

- W.M. Schmidt, Diophantine approximation, Lecture Notes in Mathematics 785, Springer Verlag 1980, Chap. V,VI,VII. Via leanprover/lean-eval@38361be, problem `schmidt_subspace`.
