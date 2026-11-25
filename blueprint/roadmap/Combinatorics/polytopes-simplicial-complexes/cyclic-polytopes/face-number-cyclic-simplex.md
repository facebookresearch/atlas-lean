# Face numbers of a cyclic simplex

For $d + 1$ distinct parameters, the simplex $C_d(d+1)$ has

$$f_k = \binom{d+1}{k+1}$$

faces of dimension $k$, for every $k \ge 0$ (in particular $f_d = 1$ and $f_k = 0$ for $k > d$).
For $d = 2$ this is a triangle, with f-vector $(f_0, f_1) = (3, 3)$; for $d = 4$ the f-vector is
$(5, 10, 10, 5)$, as in the PCMI notes, Lecture 4. These values satisfy the Euler–Poincaré relation
and attain the upper bound theorem with $n = d + 1$ vertices.

This is a concrete computation with the face-number function used by the Euler–Poincaré relation,
the upper bound theorem, Steinitz's lemma and the simplicial-sphere bridge, and it shows that the
function computes the expected values. (Balinski's and Steinitz's theorems use the graph and the
dimension of the polytope, not its face numbers.)

## Sources

- G. M. Ziegler, "Convex polytopes: extremal constructions and f-vector shapes", IAS/Park City Mathematics Series, Volume 14 (2004), arXiv:math/0411400v2 (7 December 2005). Numbering as in this arXiv version, which is the version read; the published version was not consulted. Example 2.4 (face numbers of a simplex) and Lecture 4 (f-vector of the 4-simplex).
