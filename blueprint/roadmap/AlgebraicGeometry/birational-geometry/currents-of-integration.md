# Currents of integration and the support theorems

This node is still to be broken down. It covers the facts about currents on complex manifolds on which
the [Poincaré–Lelong formula](poincare-lelong-formula.md) and its integrated form rest.

Let $X$ be a complex manifold of dimension $n$ and $A \subset X$ a closed analytic subset of pure
dimension $p$. Integration over the regular locus, $\langle [A], \alpha \rangle = \int_{A_{\mathrm{reg}}}
\alpha$ for smooth compactly supported $(p, p)$-forms $\alpha$, converges and defines a closed positive
current $[A]$ of bidimension $(p, p)$ (Lelong). A closed current of order zero and bidimension $(p, p)$
supported in an analytic set of dimension less than $p$ is zero; a closed current of order zero of
bidimension $(p, p)$ supported in $A$ is a combination $\sum_j \lambda_j [A_j]$ of the currents of the
irreducible components of $A$, with constant coefficients (support theorems).

## Depends on

Its statement uses the notions listed under Expansion.

## Proof depends on

Its proof uses the inputs listed under Expansion.

## Expansion

A good expansion has pages for:

- currents on manifolds, their derivatives defined by duality, push-forwards by proper maps and
  pull-backs by submersions (Demailly, *Complex Analytic and Differential Geometry*, Chapter I, §2);
- positive forms and positive currents (Chapter III, §1);
- Lelong's theorem on currents of integration, with the local finiteness of the volume of
  $A_{\mathrm{reg}}$ near $A_{\mathrm{sing}}$ (Chapter III, (2.5)–(2.7)), and the Skoda–El Mir
  extension theorem (Demailly, *Analytic Methods*, Theorem (1.18));
- the first and second support theorems and their corollaries (Chapter III, (2.10)–(2.14));
- the fundamental solution $\frac{i}{\pi} \partial\bar\partial \log |z| = \delta_0$ on $\mathbb{C}$
  (Chapter I, Corollary 3.4).

A good expansion also states and links:

- closed analytic subsets of complex manifolds, their regular loci and currents on complex manifolds
  (Demailly, *Complex Analytic and Differential Geometry*, Chapter I, §2, and Chapter II, §4), for
  the statement
- decomposable test forms and the finite ramified projections of $A$ onto coordinate subspaces
  (Chapter II, Proposition (4.8) and the local parametrization theorem (4.19), which the proof of
  Chapter III, (2.6), cites as II.3.8 and II.3.19), for the local finiteness of the volume of
  $A_{\mathrm{reg}}$ near $A_{\mathrm{sing}}$ in Lelong's theorem (Chapter III, (2.6)–(2.7)), whose
  closedness of $[A]$ comes from the Skoda–El Mir extension theorem across the pluripolar set
  $A_{\mathrm{sing}}$
- the local structure of currents of order zero along a submanifold and their normal order, for the
  support theorems (Chapter III, (2.10)–(2.14))

## Sources

- J.-P. Demailly, *Complex Analytic and Differential Geometry*, version of 21 June 2012,
  <https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/agbook.pdf>: Chapter I, §2 and
  Corollary 3.4; Chapter III, §1, (2.5)–(2.7), First theorem of support (2.10), Corollary (2.11),
  Second theorem of support (2.13) and Corollary (2.14), pp. 140–143.
- J.-P. Demailly, *Analytic Methods in Algebraic Geometry*, Surveys of Modern Mathematics 1, Higher
  Education Press and International Press, 2012; author's version of July 2011,
  <https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/analmeth_book.pdf>: (1.17)
  (currents of integration), p. 10, and Theorem (1.18) (Skoda–El Mir), p. 11.
