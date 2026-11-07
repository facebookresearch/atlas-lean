# Smoothing at a path vertex of a coconut tree

Let the coconut tree $CT(p + 1, s)$ have
path vertices $v_1, \dots, v_{p+1}$, central vertex $v_{p+1}$ and leaves $\ell_1, \dots, \ell_s$,
let $d$ and $r$ be labelings of its vertices by natural numbers, and let $1 \le k \le p + 1$.
Smoothing $(d, r)$ at $v_k$ gives the labelings $(d', r')$ of $CT(p, s)$ obtained by deleting
$v_k$ and renumbering the remaining path vertices $v_1, \dots, v_{k-1}, v_{k+1}, \dots, v_{p+1}$
in order as $v_1, \dots, v_p$. Every remaining vertex keeps its value of $r$ and its value of $d$,
except that $d$ drops by $1$ (truncated at $0$) at the path neighbours $v_{k-1}$ and $v_{k+1}$
of $v_k$, where they exist.

The paper applies it only at a non-central vertex ($k \le p$) with $d(v_k) = 1$: for $k \ge 2$
this is the degree-2 smoothing of Definition 3.1 and for $k = 1$ the smoothing at $v_1$ of
Definition 3.4.

## Sources

- Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definitions 3.1 and 3.4 (arXiv numbering).
