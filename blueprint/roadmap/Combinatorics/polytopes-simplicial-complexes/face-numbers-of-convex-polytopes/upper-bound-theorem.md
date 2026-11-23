# Upper bound theorem (McMullen)

Let $P = \operatorname{conv} s$ be a polytope of dimension $d$ with $m$ vertices. Then for every
$k < d$,

$$f_k(P) \le f_k(C_d(m)) = \sum_{j=0}^{k+1} \binom{d-j}{k+1-j} h_j(C_d(m)), \qquad
h_j(C_d(m)) = \binom{m-d-1+\min(j,d-j)}{\min(j, d-j)},$$

the number of $k$-dimensional faces of the cyclic polytope with $m$ vertices in dimension $d$.
The right-hand side is the bound of the upper bound theorem for simplicial spheres.

The polytope need not be simplicial, and need not be full-dimensional in the ambient space $\mathbb{R}^n$.
Example: a convex $m$-gon ($d = 2$) has $f_0 = f_1 = m$, and the formula gives
$f_0(C_2(m)) = 2 + (m - 2) = m$ and $f_1(C_2(m)) = 1 + (m - 2) + 1 = m$, so equality holds. For
$d = 4$ and $k = 1$ the bound is $f_1 \le \binom{m}{2}$, the upper bound inequality of the PCMI
notes, Lecture 4, attained by neighborly 4-polytopes such as $C_4(7)$ with
$f(C_4(7)) = (7, 21, 28, 14)$.

McMullen's proof reduces to simplicial polytopes by pulling vertices, which can only increase the
face numbers, bounds $h_j \le \binom{m-d-1+j}{j}$ for $j \le d/2$ by a shelling argument, and
obtains the remaining entries from the Dehn–Sommerville equations $h_j = h_{d-j}$.

## Informally uses

- [Dehn–Sommerville equations](../face-numbers-of-simplicial-spheres/dehn-sommerville.md): the
  symmetry $h_j = h_{d-j}$ of the boundary complex of a simplicial polytope, which turns the bound
  on the first half of the h-vector into a bound on all face numbers.

## Background

- [The boundary complex of a simplicial polytope is a simplicial sphere](exists-simplicial-sphere-face-count-eq.md):
  the passage from simplicial polytopes to their boundary complexes, where the Dehn–Sommerville
  equations are stated on this site.
- [Upper bound theorem for simplicial spheres](../upper-bound-theorem-for-simplicial-spheres/upper-bound-theorem-simplicial-spheres.md):
  Stanley's extension to all simplicial spheres; for simplicial polytopes it implies this
  statement through their boundary complexes, while non-simplicial polytopes need McMullen's
  reduction.
- [Cyclic polytopes are neighborly](../cyclic-polytopes/is-exposed-cyclic-polytope-of-two-mul-ca.md):
  the neighborliness that makes the cyclic polytope attain the bound.

## Sources

- P. McMullen, "The maximum numbers of faces of a convex polytope", Mathematika 17 (1970), 179–184 (not read; the statement is the one quoted in the PCMI notes, Lecture 1, and in Lecture 4 for $d = 4$).
- G. M. Ziegler, "Convex polytopes: extremal constructions and f-vector shapes", IAS/Park City Mathematics Series, Volume 14 (2004), arXiv:math/0411400v2 (7 December 2005). Numbering as in this arXiv version, which is the version read; the published version was not consulted. Lecture 1 (stacked and cyclic polytopes as the extremal cases of the lower and upper bound theorems) and Lecture 4.
