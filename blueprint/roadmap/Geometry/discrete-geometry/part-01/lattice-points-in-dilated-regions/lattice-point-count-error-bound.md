# Lattice-point error bound from boundary charts

Let $S \subseteq \mathbb{R}^n$ be
bounded, let $f_1, \dots, f_m$ be maps from the unit cube $[0,1]^d$ to $\mathbb{R}^n$ whose
ranges cover the boundary $\partial S$, and let $t > 0$. For each $i$, let $N_i(t)$ be the number
of $v \in \mathbb{Z}^n$ such that $t f_i(y)$ lies in the half-open cube $\prod_j [v_j, v_j + 1)$
for some $y \in [0,1]^d$, and assume each of these sets of $v$ is finite. Then the lattice
enumerator $L_S(t)$, the number of points of $\mathbb{Z}^n$ in $tS$, satisfies
$|L_S(t) - \operatorname{vol}(S)\, t^n| \le N_1(t) + \dots + N_m(t)$, where $\operatorname{vol}$
is Lebesgue (outer) measure.
