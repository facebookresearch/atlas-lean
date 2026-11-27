# Smoothing at a leaf of a coconut tree

Let the coconut tree $CT(p, s + 1)$ have path
vertices $v_1, \dots, v_p$, central vertex $v_p$ and leaves $\ell_1, \dots, \ell_{s+1}$, let $d$
and $r$ be labelings of its vertices by natural numbers, and let $1 \le k \le s + 1$. Smoothing
$(d, r)$ at the leaf $\ell_k$ gives the labelings $(d', r')$ of $CT(p, s)$ obtained by deleting
$\ell_k$ and renumbering the remaining leaves $\ell_1, \dots, \ell_{k-1}, \ell_{k+1}, \dots,
\ell_{s+1}$ in order as $\ell_1, \dots, \ell_s$. Every remaining vertex keeps its value of $r$
and its value of $d$, except that $d$ drops by $1$ (truncated at $0$) at the central vertex $v_p$
when $p \ge 1$.

## Sources

- Diaz-Lopez, Ha, Harris, Rogers, Koss and Smith, *Arithmetical Structures on Coconut Trees*, INTEGERS 25 (2025), Article A82, Definition 3.4 (arXiv numbering).
