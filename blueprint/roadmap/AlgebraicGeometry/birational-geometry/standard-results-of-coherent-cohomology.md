# Standard results of coherent cohomology on projective varieties

This node is still to be broken down. It collects the classical results of coherent cohomology and
projective geometry that the proofs of the vanishing theorems and of the asymptotic Riemann–Roch
statements use without proof. Let $X$ be a projective variety over a field $k$. The targets are:

1. the projection formula $R^q f_*(\mathcal{F} \otimes f^* \mathcal{L}) \cong R^q f_* \mathcal{F}
   \otimes \mathcal{L}$ for a morphism $f$ and a locally free sheaf $\mathcal{L}$, and the
   degeneration of the Leray spectral sequence: if $R^q f_* \mathcal{F} = 0$ for $q > 0$, then
   $H^i(X', \mathcal{F}) \cong H^i(X, f_* \mathcal{F})$;
2. Serre's vanishing theorem and Serre duality on smooth projective varieties, and GAGA over
   $\mathbb{C}$;
3. the Hirzebruch–Riemann–Roch theorem, and the fact that $\chi(X, L^{\otimes \nu})$ is a polynomial in
   $\nu$ of degree at most $\dim X$ whose coefficient of $\nu^{\dim X}$ is $(L^{\dim X})/(\dim X)!$
   (for $L = \mathcal{O}$ on $\mathbb{P}^1$ it is the constant $1$);
4. Bertini's theorem: for a smooth projective variety over an algebraically closed field of
   characteristic zero and a linear system without base points, a general member is smooth, and meets a
   given simple normal crossing divisor transversally;
5. Seshadri's criterion for ampleness, and its consequence that an invertible sheaf $L$ on a projective
   manifold is nef if and only if $L^{\nu} \otimes A$ is ample for every ample $A$ and every $\nu > 0$
   (Esnault–Viehweg, Lemma 5.7);
6. the Nakai–Moishezon criterion: a line bundle $L$ on a projective scheme is ample if and only if
   $(L^{\dim Z} \cdot Z) > 0$ for every integral closed subscheme $Z$ of positive dimension;
7. the embedding criterion: on a complete variety over an algebraically closed field, a complete linear
   system that separates points and tangent vectors defines a closed immersion into projective space
   (Milne, *Abelian Varieties*, Proposition I.6.3);
8. descent of ampleness: a complete variety over a field $k$ has an ample divisor if its extension of
   scalars to an algebraic closure of $k$ has one (Milne, Proposition I.6.6 (d)).

A good expansion has a page for each of 1–8, with the standard proofs (for instance Hartshorne,
*Algebraic Geometry*, II, Exercise 5.1, III, Exercise 8.1, Theorem 5.2, Corollary 7.7 and
Corollary 10.9, and Appendix A; Serre, "Géométrie algébrique et géométrie analytique").

## Sources

- H. Esnault and E. Viehweg, *Lectures on Vanishing Theorems*, DMV Seminar 20, Birkhäuser, 1992;
  electronic version on H. Esnault's page, <https://page.mi.fu-berlin.de/esnault/books/esvibuch.pdf>
  (page numbers of the electronic version): Theorem 1.1 (Serre vanishing), p. 4; Lemma 5.7 (via
  Seshadri's criterion) and the proof of Lemma 5.8 (Hirzebruch–Riemann–Roch, hyperplane sections),
  pp. 46–47; 8.1 (GAGA and flat base change), p. 82.
- R. Lazarsfeld, "A short course on multiplier ideals", arXiv:0901.0651 (version 1),
  <https://arxiv.org/abs/0901.0651v1>: the proof of Theorem 2.4 (projection formula and the Leray
  spectral sequence), pp. 11–12.
- R. Hartshorne, *Algebraic Geometry*, Graduate Texts in Mathematics 52, Springer, 1977: as cited
  above.
- J. S. Milne, *Abelian Varieties*, course notes, version 2.00 (2008),
  <https://www.jmilne.org/math/CourseNotes/AV.pdf>: Chapter I, Propositions 6.3 and 6.6 (d).
