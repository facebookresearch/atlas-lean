# Belief propagation is exact on trees

Let $m$ be a pairwise tree model on the vertices
$0, \dots, n$ with values in a finite type $\alpha$, let $w$ be its unnormalized weight, and let
$b_v$ be the belief of vertex $v$ computed by sum-product message passing. Then for every vertex
$v$ and every function $g : \alpha \to \mathbb{R}$,

$$\sum_x w(x)\, g(x_v) = \sum_{a \in \alpha} b_v(a)\, g(a),$$

where $x$ ranges over all assignments of values in $\alpha$ to the vertices.
