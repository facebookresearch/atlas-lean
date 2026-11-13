# Counting outer cubes by inner cubes and boundary charts

Let $S \subseteq \mathbb{R}^n$,
let $f_1, \dots, f_m : [0,1]^d \to \mathbb{R}^n$ be maps whose ranges together cover the frontier
of $S$, and let $t$ be a real number. Let $O$ and $I$ be the outer and inner cube sets of $S$ at
scale $t$: the $v \in \mathbb{Z}^n$ for which some, respectively every, point $x$ of the half-open
unit cube $\prod_i [v_i, v_i + 1)$ has $x / t \in S$ (coordinatewise, with $x / 0 = 0$). Let $C_i$
be the integer cube set of $f_i$ at scale $t$: the $v$ whose half-open unit cube contains
$t f_i(y)$ for some $y \in [0,1]^d$. If $O$ and every $C_i$ are finite, then
$|O| \le |I| + \sum_{i=1}^m |C_i|$.
