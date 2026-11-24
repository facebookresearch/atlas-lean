# Artin symbols act on the j-invariants of CM lattices

Let $K \subset \mathbb{C}$ be an imaginary quadratic field with ring of integers $\mathcal{O}_K$. A
fractional ideal $\mathfrak{a}$ of $K$ is a lattice in $\mathbb{C}$; let $j(\mathfrak{a})$ be the
$j$-invariant of the elliptic curve $\mathbb{C}/\mathfrak{a}$, that is,
$j(\mathfrak{a}) = 1728\, g_2(\mathfrak{a})^3 / (g_2(\mathfrak{a})^3 - 27\, g_3(\mathfrak{a})^2)$ with
$g_2$ and $g_3$ the Eisenstein invariants of the lattice. Let $H \subset \mathbb{C}$ be a Hilbert class
field of $K$. Then $j(\mathfrak{a}) \in H$ for every fractional ideal $\mathfrak{a}$, and for all
fractional ideals $\mathfrak{a}$ and $\mathfrak{b}$ of $K$

$$\mathrm{art}_{H/K}(\mathfrak{b})\bigl(j(\mathfrak{a})\bigr) = j(\mathfrak{b}^{-1}\mathfrak{a}),$$

where $\mathrm{art}_{H/K}$ is the Artin map of $H/K$. Since $H/K$ is abelian and unramified at every
prime, the Artin map is defined on the whole group of fractional ideals and sends a prime ideal
$\mathfrak{p}$ to its Frobenius element.

Milne states the formula for prime ideals, $\mathrm{Frob}(\mathfrak{p})(j(\mathfrak{a})) =
j(\mathfrak{a}\mathfrak{p}^{-1})$, as part (c) of his Theorem 12.18, whose part (a) says that
$K(j(\mathfrak{a}))$ is the Hilbert class field; the formula for all $\mathfrak{b}$ follows because
the Artin map is a homomorphism. Since $j(\mathfrak{a})$ depends only on the ideal class of
$\mathfrak{a}$, two elliptic curves are isomorphic exactly when their $j$-invariants agree, and the
Artin map induces an isomorphism from the class group of $K$ onto $\mathrm{Gal}(H/K)$ (reciprocity),
the formula says that $\mathrm{Gal}(H/K)$ permutes the $h_K$ distinct values $j(\mathfrak{a})$ simply
transitively; Milne's part (b) of Theorem 12.18 states the transitivity.

Milne's proof reduces elliptic curves with complex multiplication modulo primes. For an elliptic
curve $E$ with complex multiplication by $\mathcal{O}_K$, defined over a number field $L$, and a prime
$\mathfrak{p}$ of $K$ of degree one at which $L/K$ is unramified and $E$ has good reduction, the
$\mathfrak{p}$-isogeny $E \to \mathfrak{p} * E$ onto the quotient of $E$ by its $\mathfrak{p}$-torsion
(for $E = \mathbb{C}/\mathfrak{a}$ this is $\mathbb{C}/\mathfrak{p}^{-1}\mathfrak{a}$) reduces to a
purely inseparable isogeny of degree $N\mathfrak{p}$, hence to the Frobenius map; this gives the
formula for a set of primes of density one (Lemma 12.25). Class field theory, through the reciprocity
law, then identifies the Galois action with the Artin map.

## Depends on

- [Hilbert class field of a number field](is-hilbert-class-field.md)
- [Artin map](../artin-map/artin-map.md)

## Proof depends on

- [Global reciprocity law](../reciprocity-law/global-reciprocity-law.md), for the isomorphism from the class group of $K$ onto $\mathrm{Gal}(H/K)$ induced by the Artin map
- [The global Artin map at unramified places](../reciprocity-law/artin-map-at-unramified-places.md), which identifies the global Artin map of $H/K$ with its Artin map on ideals
- [Existence theorem of global class field theory](../existence-theorem/existence-of-class-fields.md), for an unramified abelian extension of $K$ of degree the class number, the class field of the idèles that are units at all finite places, so that the kernel of the Artin map of $H/K$ is the group of principal ideals

## Sources

- J. S. Milne, *Modular Functions and Modular Forms*, version 1.31 (2017),
  <https://www.jmilne.org/math/CourseNotes/MF.pdf>, Chapter 12: Theorem 12.18 (c) and (b), with
  Propositions 12.3, 12.6 and 12.20, Theorem 12.8, Corollary 12.16 and Lemma 12.25 (the proof). The
  proof in these notes is incomplete. Proposition 12.21 says that the class group acts simply
  transitively on the isomorphism classes of elliptic curves with complex multiplication by
  $\mathcal{O}_K$; this is to be read for geometric isomorphism classes, that is, over an algebraically
  closed field (over $\mathbb{Q}(i)$, whose class group is trivial, $y^2 = x^3 - x$ and $y^2 = x^3 - 3x$
  both have complex multiplication by $\mathbb{Z}[i]$ but are not isomorphic). Milne proves it for
  $\mathbb{C}$ only: "We omit the proof of the general case, although this is a key point."
- Provenance: Alpöge's Lean library (<https://alpo.ge/remark.pdf>; source mirror
  <https://github.com/leanprover-community/riemann-hypothesis/tree/79c751e0b0a5ea3bbfc20198c852fa85f28661e6>) uses this result, as `GroundTheory.Global.Elliptic.hilbertClassFieldArtinEquiv_apply_j`.
