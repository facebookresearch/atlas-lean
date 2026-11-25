# Left repair after double-black deletion

Write $\mathrm{R}$ and $\mathrm{B}$ for red and
black, and $N(c, T, y, T')$ for the node of color $c$ with left subtree $T$, key $y$ and right
subtree $T'$. Given a color $c$, a tree $D$, a key $k$ and a tree $S$, the left repair returns a
tree whose root may be double black, by the first case that applies. If
$S = N(\mathrm{B}, T_1, y, N(\mathrm{R}, T_2, z, T_3))$ or, failing that,
$S = N(\mathrm{B}, N(\mathrm{R}, T_1, y, T_2), z, T_3)$, it returns
$N(c, N(\mathrm{B}, D, k, T_1), y, N(\mathrm{B}, T_2, z, T_3))$. Otherwise, if
$S = N(\mathrm{B}, T_1, y, T_2)$, it returns $N(\mathrm{B}, D, k, N(\mathrm{R}, T_1, y, T_2))$ when
$c$ is red, and the double-black node with left child $D$, key $k$ and right child
$N(\mathrm{R}, T_1, y, T_2)$ when $c$ is black. In the next three cases $c$ is not used. If
$S = N(\mathrm{R}, N(\mathrm{B}, T_1, y, N(\mathrm{R}, T_2, z, T_3)), w, T_4)$ or, failing that,
$S = N(\mathrm{R}, N(\mathrm{B}, N(\mathrm{R}, T_1, y, T_2), z, T_3), w, T_4)$, it returns
$N(\mathrm{B}, N(\mathrm{R}, N(\mathrm{B}, D, k, T_1), y, N(\mathrm{B}, T_2, z, T_3)), w, T_4)$.
Otherwise, if $S = N(\mathrm{R}, N(\mathrm{B}, T_1, y, T_2), w, T_3)$, it returns
$N(\mathrm{B}, N(\mathrm{B}, D, k, N(\mathrm{R}, T_1, y, T_2)), w, T_3)$. In every remaining case
it returns $N(c, D, k, S)$.

The repair is meant for a deficient left subtree $D$ whose double black has been absorbed, so
that $D$ has one black node fewer than its sibling $S$ on every root-to-leaf path.
