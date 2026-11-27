# Gale's evenness criterion

Let $t_1 < t_2 < \cdots < t_n$ be real numbers and let $S$ be a set of $d$ indices. Then the
points $\gamma(t_i)$, $i \in S$, span a face of the cyclic polytope
$C_d(n) = \operatorname{conv}\{\gamma(t_1), \dots, \gamma(t_n)\} \subset \mathbb{R}^d$, that is,
$\operatorname{conv}\{\gamma(t_i) : i \in S\}$ is a face of $C_d(n)$, if and only if $S$ satisfies
Gale's evenness condition. Since $d$ points of the moment curve are affinely independent, for
$n > d$ such a face is a facet, so the criterion lists the facets of $C_d(n)$; in particular the combinatorial
type of $C_d(n)$ does not depend on the parameters.

Proof. A linear functional $\ell$ on $\mathbb{R}^d$ restricted to the moment curve is a polynomial
$\ell(\gamma(\tau))$ of degree at most $d$ without constant term, and every such polynomial
arises. If the face is cut out by $\ell$ with maximum $V$, the polynomial
$g(\tau) = V - \ell(\gamma(\tau))$ vanishes at the $d$ points $t_i$, $i \in S$, and is positive
at the other $t_j$ (a point $\gamma(t_j)$, $j \notin S$, on the face would lie in the convex hull of
the $\gamma(t_i)$, which a degree-$d$ polynomial vanishing exactly on $S$ rules out). Hence
$g = c \prod_{i \in S} (\tau - t_i)$, whose sign at $t_j$ is that of $c$ times
$(-1)^{|\{i \in S : i > j\}|}$; constant sign at all $j \notin S$ is the evenness condition.
Conversely, under the evenness condition $\pm \prod_{i \in S} (\tau - t_i)$, with the sign chosen
negative at the $t_j$, $j \notin S$, comes from a functional cutting out exactly this face. This is
the argument sketched in the PCMI notes, where a hyperplane through $d$ points of the curve meets
it in no other point.

Degenerate cases are covered: for $n = d$ the only set is $S = \{0, \dots, n-1\}$, the condition is
vacuous and the face is $C_d(n)$ itself; for $d = 0$, $S = \emptyset$ and the face is empty.

## Sources

- G. M. Ziegler, "Convex polytopes: extremal constructions and f-vector shapes", IAS/Park City Mathematics Series, Volume 14 (2004), arXiv:math/0411400v2 (7 December 2005). Numbering as in this arXiv version, which is the version read; the published version was not consulted. Example 2.6. The statement there is informal (facets correspond to $d$-subsets whose elements split into adjacent pairs, for $d$ even and indices read cyclically); the version here is the usual form of Gale's evenness criterion, valid for all $d$.
- D. Gale, "Neighborly and cyclic polytopes", in *Convexity*, Proc. Sympos. Pure Math. 7, American Mathematical Society, 1963 (reference [30] of the PCMI notes; not read).
