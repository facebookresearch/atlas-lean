# Integer cube set

Let $f$ be a map from the unit cube $[0, 1]^d$ to $\mathbb{R}^n$ and let
$t$ be a real number. The integer cube set of $f$ at scale $t$ is the set of integer vectors
$v \in \mathbb{Z}^n$ for which some point $y$ of the unit cube satisfies
$v_i \le t f(y)_i < v_i + 1$ for every coordinate $i$, that is, the set of integer vectors whose
half-open unit cube $\prod_i [v_i, v_i + 1)$ meets the dilate $t \cdot f([0, 1]^d)$.
