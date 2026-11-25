# Steinitz's lemma: the f-vectors of 3-polytopes

A triple $(f_0, f_1, f_2)$ of natural numbers is the f-vector of a 3-dimensional convex polytope
(a finite point set in $\mathbb{R}^3$ whose convex hull has nonempty interior) if and only if

$$f_0 - f_1 + f_2 = 2, \qquad f_2 \le 2 f_0 - 4, \qquad f_0 \le 2 f_2 - 4.$$

So the f-vectors of 3-polytopes are exactly the integer points of a 2-dimensional polyhedral cone
with apex $(4, 6, 4)$, the f-vector of the tetrahedron. The first condition is Euler's equation,
the second is the upper bound inequality, with equality exactly for simplicial polytopes, and the
third is its dual, with equality exactly for simple polytopes.

The PCMI notes state the lemma for integer triples; the three conditions force $f_0, f_2 \ge 4$
and $f_1 \ge 6$, so restricting to natural numbers loses nothing. The inequalities follow from
Euler's equation and double counting ($2 f_1 \ge 3 f_2$, $2 f_1 \ge 3 f_0$); the converse
constructs a polytope for each such triple.

## Informally uses

- [Euler–Poincaré relation](euler-poincare.md): the case $d = 3$, Euler's equation, which together
  with double counting of edge–facet and edge–vertex incidences gives the two inequalities.

## Sources

- G. M. Ziegler, "Convex polytopes: extremal constructions and f-vector shapes", IAS/Park City Mathematics Series, Volume 14 (2004), arXiv:math/0411400v2 (7 December 2005). Numbering as in this arXiv version, which is the version read; the published version was not consulted. Lemma 1.1 and Section 1.1; the notes leave the proof as Exercise 1.3.
- E. Steinitz (1906), reference [73] of the PCMI notes (not read).
