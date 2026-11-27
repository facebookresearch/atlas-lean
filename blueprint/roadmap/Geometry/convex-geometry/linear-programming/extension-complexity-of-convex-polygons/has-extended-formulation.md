# Extended formulations of planar sets (bounded linear lifts)

A set $P \subseteq \mathbb{R}^2$ has an extended formulation of size $r \in \mathbb{N}$ when there are $m \in \mathbb{N}$, vectors $a_1, \dots, a_r \in \mathbb{R}^m$, reals $b_1, \dots, b_r$ and a linear map $\pi : \mathbb{R}^m \to \mathbb{R}^2$ such that the set

$$Q = \{y \in \mathbb{R}^m : a_i \cdot y \le b_i \text{ for } i = 1, \dots, r\}$$

is bounded and $\pi(Q) = P$. So $P$ is a linear projection of a polytope described by $r$ linear inequalities. This is the bounded, linear, inequality-only convention: the lift $Q$ is given by $r$ ambient inequalities and must be bounded, and the projection is linear. The usual definition instead counts the facets of a polytope mapped affinely onto $P$, and the two can differ for sets that are not full-dimensional: for $P = [0, 1] \times \{1\}$ the interval $[0, 1]$ with $t \mapsto (t, 1)$ is a usual extension with two facets, but no bounded set given by two inequalities projects linearly onto $P$. For a convex polygon with nonempty interior the two agree: write the lift in coordinates of its affine hull, where its facets describe it; the linear part of the affine projection is then onto $\mathbb{R}^2$, so a translation of the lift absorbs the offset.
