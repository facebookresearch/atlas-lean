# Subdivision at a path vertex of a coconut tree

Let the coconut tree $CT(p, s)$ have path
vertices $v_1, \dots, v_p$ and leaves $\ell_1, \dots, \ell_s$, let $d$ and $r$ be labelings of
its vertices by natural numbers, and let $1 \le k \le p$. Subdividing $(d, r)$ at position $k$
gives the labelings $(d', r')$ of $CT(p + 1, s)$ obtained by inserting a new path vertex $w$
just before $v_k$, so that the path becomes $v_1, \dots, v_{k-1}, w, v_k, \dots, v_p$, with
$d'(w) = 1$ and $r'(w) = r(v_{k-1}) + r(v_k)$, where $r(v_0) = 0$ (so $r'(w) = r(v_1)$ when
$k = 1$). The path neighbours of $w$, namely $v_{k-1}$ (when $k \ge 2$) and $v_k$, get
$d' = d + 1$; every other vertex keeps its value of $d$, and every vertex other than $w$ keeps
its value of $r$.

## Sources

- Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 3.9 (arXiv numbering).
