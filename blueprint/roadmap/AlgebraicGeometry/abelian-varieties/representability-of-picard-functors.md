# Representability of relative Picard functors

This node is still to be broken down. It covers the representability theorems for relative Picard
functors, and the bound on the cohomology of the structure sheaf of a group variety, that the
constructions of the [dual abelian variety](dual-abelian-variety.md) and of the
[dual abelian scheme](dual-abelian-scheme.md) use.

For a morphism $f \colon X \to S$ the relative Picard functor $\mathcal{P}ic_{X/S}$ is the fppf
sheaf associated with $T \mapsto \operatorname{Pic}(X \times_S T)$. If $f$ is proper, flat and of
finite presentation, $\mathcal{O}_T \cong f_{T*} \mathcal{O}_{X_T}$ for every $S$-scheme $T$ (a
universal $\mathcal{O}$-morphism), and $f$ has a section $e$, then $\mathcal{P}ic_{X/S}(T)$ is the
group of isomorphism classes of line bundles on $X \times_S T$ rigidified along $e_T$. The targets
are:

1. (Artin; Raynaud.) If $f$ is proper, flat, locally of finite presentation and cohomologically flat
   in dimension zero, $\mathcal{P}ic_{X/S}$ is a quasi-separated algebraic space; if moreover $f$ is
   a universal $\mathcal{O}$-morphism with a section, there is a universal rigidified line bundle on
   $X \times_S \mathcal{P}ic_{X/S}$; its Lie algebra is $R^1 f_* \mathcal{O}_X$; if the geometric
   fibres are integral it is separated, and if moreover $f$ is smooth its closed subspaces of finite
   type over $S$ are proper (Robert, Theorem 2.3.4 (i)–(iii), (v)).
2. (Grothendieck.) If $f$ is projective, flat, of finite presentation with integral geometric
   fibres, $\mathcal{P}ic_{X/S}$ is a separated scheme locally of finite presentation over $S$, a
   disjoint union of quasi-projective pieces indexed by Hilbert polynomials (Robert, Theorem 2.3.4
   (vi)).
3. Over a field $k$, for $X$ proper and geometrically reduced, $\mathcal{P}ic_{X/k}$ is a scheme
   locally of finite type, separated if $X$ is geometrically integral; if $X$ is smooth and
   geometrically connected its identity component is proper, and projective if $X$ is projective, of
   dimension at most $\dim_k H^1(X, \mathcal{O}_X)$, with equality exactly when it is smooth
   (Robert, Corollary 2.3.5).
4. (Raynaud.) An abelian algebraic space over a scheme is an abelian scheme (Robert, Theorem 2.3.2).
5. For an abelian variety $X$ over a field $k$, $H^\bullet(X, \mathcal{O}_X)$ is a
   graded-commutative bialgebra of finite type with $H^0(X, \mathcal{O}_X) = k$, and $\dim_k H^1(X,
   \mathcal{O}_X) \le \dim X$ (van der Geer–Moonen, Proposition (6.15), through the Borel–Hopf
   structure theorem (6.12) and Corollary (6.13), for a connected graded bialgebra of finite type).
   Van der Geer and Moonen state (6.15) for group varieties, but the bound fails without properness:
   for an elliptic curve $E$ over $\mathbb{C}$ and $X = E \times \mathbb{G}_a$, the projection to
   $E$ is affine with direct image $\mathcal{O}_E[t]$, so $H^0(X, \mathcal{O}_X) = \mathbb{C}[t]$
   and $H^1(X, \mathcal{O}_X) = H^1(E, \mathcal{O}_E) \otimes \mathbb{C}[t]$ is
   infinite-dimensional, while $\dim X = 2$. For a proper geometrically connected group variety, as
   for an abelian variety, $H^0 = k$ and all the $H^i$ are finite-dimensional, which is what the
   argument uses.

A good expansion has pages for: Artin's representability criterion for algebraic spaces and its
application to Picard functors; Grothendieck's construction through Hilbert and Quot schemes in the
projective case; Raynaud's theorem; and the passage from a quasi-separated group algebraic space
over a field to a scheme, through its dense schematic open subspace.

## Depends on

- [Abelian scheme](abelian-scheme.md), for the abelian schemes of 4 and the abelian varieties of 5
- [The fppf topology on schemes](../grothendieck-topologies/fppf-topology-on-schemes.md), for the
  fppf sheaves in which the statement places the relative Picard functors
- [The topology induced on an over category](../../CategoryTheory/sites-and-sheaves/topology-on-an-over-category.md),
  for the fppf site of schemes over $S$, on which the relative Picard functors are sheaves,
  evaluated at $S$-schemes $T \to S$

## Proof depends on

- [Standard results of coherent cohomology on projective varieties](../birational-geometry/standard-results-of-coherent-cohomology.md),
  for the finiteness of coherent cohomology on a proper scheme over a field and its invariance under
  extension of the base field (item 2), by which van der Geer and Moonen pass to an algebraic
  closure in 5 ((6.14)–(6.15))

## Expansion

A good expansion also states and links:

- algebraic spaces over $S$, or over $T$ after base change along $T \to S$, presented as quotients
  of étale equivalence relations (stated in the project as
  `AlgebraicGeometry.GeneralStackGeometry.AlgebraicSpaceOver`,
  MathlibExt/AlgebraicGeometry/GeneralStackGeometry.lean:181–185, and
  `AlgebraicGeometry.EtaleSpacePresentations.EtaleEquivalencePresentation`,
  MathlibExt/AlgebraicGeometry/EtaleSpacePresentations.lean:65–76), in which the statement places
  the relative Picard functors defined above, for the statement
- the Künneth formula for the cohomology of the structure sheaf, which gives the coproduct, and the
  vanishing of coherent cohomology above the dimension (van der Geer–Moonen, (6.14)–(6.15)), for 5
- the Borel–Hopf structure theorem for graded bialgebras over a perfect field (van der Geer–Moonen,
  (6.12)–(6.13)), for 5

## Sources

- D. Robert, *Theory of abelian varieties and their moduli spaces*, draft book (version of 7 March
  2023), <https://www.math.u-bordeaux.fr/~damienrobert/pro/publications/books/avtheory.pdf>: §2.3.2,
  the definition of $\mathcal{P}ic_{X/S}$, the exact sequences (2.2)–(2.4) and rigidified line
  bundles, Theorem 2.3.4 with its proof, Corollary 2.3.5 with its proof, and Theorem 2.3.2 with its
  proof, pp. 12–14.
- G. van der Geer and B. Moonen, *Abelian Varieties*, book draft, Chapter VI, "The Picard scheme of
  an abelian variety", <https://www.math.ru.nl/personal/bmoonen/BookAV/DualAV1.pdf>: §1 (relative
  Picard functors, admitted from the general theory), Corollary (6.6), §2 with Theorem (6.12),
  Corollary (6.13) and Proposition (6.15), and the beginning of §3, pp. 85–95.
- S. Bosch, W. Lütkebohmert and M. Raynaud, *Néron Models*, Ergebnisse der Mathematik (3) 21,
  Springer, 1990: Chapter 8, as cited by Robert.
