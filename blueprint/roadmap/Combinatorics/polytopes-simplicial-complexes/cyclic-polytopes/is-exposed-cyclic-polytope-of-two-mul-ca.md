# Cyclic polytopes are neighborly

Let $t_1, \dots, t_n$ be distinct real numbers and let $T$ be a set of indices with
$2|T| \le d$. Then $\operatorname{conv}\{\gamma(t_i) : i \in T\}$ is a face of the cyclic polytope
$C_d(n) \subset \mathbb{R}^d$. In particular every set of at most $\lfloor d/2 \rfloor$ vertices of
$C_d(n)$ spans a face: $C_d(n)$ is $\lfloor d/2 \rfloor$-neighborly. Since such vertex sets are
affinely independent, it follows that $f_{k-1}(C_d(n)) = \binom{n}{k}$ for $k \le d/2$.

Proof: for $T = \emptyset$ the face is the empty face. For nonempty $T$, the polynomial $-\prod_{i \in T}(\tau - t_i)^2$ has degree $2|T| \le d$, is at most $0$,
and vanishes exactly at the $t_i$, $i \in T$; the corresponding linear functional attains its
maximum over $C_d(n)$ exactly on the convex hull of these points.

## Background

- [Upper bound theorem (McMullen)](../face-numbers-of-convex-polytopes/upper-bound-theorem.md):
  neighborliness is why cyclic polytopes have the largest face numbers.

## Sources

- G. M. Ziegler, "Convex polytopes: extremal constructions and f-vector shapes", IAS/Park City Mathematics Series, Volume 14 (2004), arXiv:math/0411400v2 (7 December 2005). Numbering as in this arXiv version, which is the version read; the published version was not consulted. Example 2.6. (neighborliness of cyclic polytopes).
- D. Gale, "Neighborly and cyclic polytopes", in *Convexity*, Proc. Sympos. Pure Math. 7, American Mathematical Society, 1963 (reference [30] of the PCMI notes; not read).
