# Right repair after double-black deletion

Write $\mathrm{R}$ and $\mathrm{B}$ for red and
black, and $N(c, T, y, T')$ for the node of color $c$ with left subtree $T$, key $y$ and right
subtree $T'$. Given a color $c$, a tree $S$, a key $k$ and a tree $D$, the right repair returns a
tree whose root may be double black, by the first case that applies. If
$S = N(\mathrm{B}, N(\mathrm{R}, T_1, y, T_2), z, T_3)$ or, failing that,
$S = N(\mathrm{B}, T_1, y, N(\mathrm{R}, T_2, z, T_3))$, it returns
$N(c, N(\mathrm{B}, T_1, y, T_2), z, N(\mathrm{B}, T_3, k, D))$. Otherwise, if
$S = N(\mathrm{B}, T_1, y, T_2)$, it returns $N(\mathrm{B}, N(\mathrm{R}, T_1, y, T_2), k, D)$ when
$c$ is red, and the double-black node with left child $N(\mathrm{R}, T_1, y, T_2)$, key $k$ and
right child $D$ when $c$ is black. In the next three cases $c$ is not used. If
$S = N(\mathrm{R}, T_1, y, N(\mathrm{B}, N(\mathrm{R}, T_2, z, T_3), w, T_4))$ or, failing that,
$S = N(\mathrm{R}, T_1, y, N(\mathrm{B}, T_2, z, N(\mathrm{R}, T_3, w, T_4)))$, it returns
$N(\mathrm{B}, T_1, y, N(\mathrm{R}, N(\mathrm{B}, T_2, z, T_3), w, N(\mathrm{B}, T_4, k, D)))$.
Otherwise, if $S = N(\mathrm{R}, T_1, y, N(\mathrm{B}, T_2, z, T_3))$, it returns
$N(\mathrm{B}, T_1, y, N(\mathrm{B}, N(\mathrm{R}, T_2, z, T_3), k, D))$. In every remaining case
it returns $N(c, S, k, D)$.

The repair is the mirror image of the left repair, meant for a deficient right subtree $D$ whose
double black has been absorbed, so that $D$ has one black node fewer than its sibling $S$ on
every root-to-leaf path.
