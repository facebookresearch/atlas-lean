# Cyclic étale coverings and torsion line bundles

This node is still to be broken down: the statement is precise, but its proof is not.

Let $k$ be a separably closed field, $V$ a complete connected nonsingular variety over $k$, $P$ a
point of $V$, and $n \ge 1$ an integer not divisible by the characteristic of $k$. Write
$\operatorname{Pic}(V)_n$ for the subgroup of elements of $\operatorname{Pic}(V)$ killed by $n$.

1. (Coverings.) There is a bijection
   $\operatorname{Hom}_{\mathrm{cont}}(\pi_1(V, P), \mathbb{Z}/n\mathbb{Z}) \cong \operatorname{Pic}(V)_n$,
   which Milne writes as an isomorphism. A divisor $D$ with $nD = \operatorname{div}(g)$, where
   $g \in k(V)^\times$, corresponds to the normalization of $V$ in the Kummer extension
   $k(V)(g^{1/n})$, which is étale over $V$; every Galois covering of $V$ with group
   $\mathbb{Z}/n\mathbb{Z}$ is obtained in this way.
2. (Cohomological form.) The Kummer sequence $0 \to \mu_n \to \mathbb{G}_m \to \mathbb{G}_m \to 0$,
   with $t \mapsto t^n$ on the right, is exact on $V_{\mathrm{et}}$. With
   $H^1(V_{\mathrm{et}}, \mathbb{G}_m) = \operatorname{Pic}(V)$ and
   $H^0(V, \mathcal{O}_V^\times) = k^\times$, which is $n$-divisible, its cohomology sequence gives an
   isomorphism $H^1(V_{\mathrm{et}}, \mu_n) \cong \operatorname{Pic}(V)_n$.

As $k$ contains $n$ distinct $n$-th roots of $1$, the choice of a primitive one identifies $\mu_n$
with the constant sheaf $\mathbb{Z}/n\mathbb{Z}$, and
[first cohomology with finite coefficients](etale-fundamental-group-and-first-cohomology.md)
identifies $H^1(V_{\mathrm{et}}, \mathbb{Z}/n\mathbb{Z})$ with
$\operatorname{Hom}_{\mathrm{cont}}(\pi_1(V, P), \mathbb{Z}/n\mathbb{Z})$; so 2 also gives a bijection
as in 1, and in either form the two groups have the same number of elements.

## Expansion

This node is still to be broken down. A good expansion states and links:

- the exactness of the Kummer sequence on the étale site (Milne, *Lectures on Étale Cohomology*,
  Example 7.9; the Stacks Project, Lemma 59.28.1);
- the isomorphism $H^1(X_{\mathrm{et}}, \mathbb{G}_m) \cong \operatorname{Pic}(X)$ (the same notes,
  Corollary 11.6), and the long exact cohomology sequence of the Kummer sequence (the Stacks
  Project, Section 59.28, after Lemma 59.28.1);
- $H^0(V, \mathcal{O}_V^\times) = k^\times$ for a complete connected variety $V$ over the separably
  closed field $k$ (the Stacks Project, Lemma 33.9.3: $H^0(V, \mathcal{O}_V)$ is a finite separable
  field extension of $k$, as $V$ is proper, connected and geometrically reduced, a variety in
  Milne's sense being geometrically reduced), and the $n$-divisibility of $k^\times$;
- for the proof of 1 through coverings, Kummer theory for $k(V)$ and the purity theorem that Milne
  cites (Grothendieck, SGA 1, X 3.1), by which the normalization of $V$ in $k(V)(g^{1/n})$ is étale.

## Depends on

- [The étale fundamental group and first étale cohomology with finite coefficients](etale-fundamental-group-and-first-cohomology.md),
  for $\pi_1(V, P)$ and the identification of $H^1$ with homomorphisms from it
- [Kummer Exactness](../not-yet-classified/small-etale-torsion-coefficients/kummer-exactness.md), for
  the Kummer sequence on the small étale site and its exactness

## Proof depends on

- [The étale fundamental group and first étale cohomology with finite coefficients](etale-fundamental-group-and-first-cohomology.md),
  for the classification of the Galois coverings of $V$ with group $\mathbb{Z}/n\mathbb{Z}$ by the
  continuous homomorphisms $\pi_1(V, P) \to \mathbb{Z}/n\mathbb{Z}$ (its items 1 and 2), in the proof
  of 1 and in passing between the two forms

## Sources

- J. S. Milne, *Abelian Varieties*, course notes, version 2.00 (2008), <https://www.jmilne.org/math/CourseNotes/AV.pdf>: Chapter III, Lemma 9.2 and its proof, p. 114; for a proof through étale cohomology Milne
  refers to his *Étale Cohomology*, III 4.11.
- J. S. Milne, *Lectures on Étale Cohomology*, course notes, version 2.21 (2013), <https://www.jmilne.org/math/CourseNotes/LEC.pdf>: Example 7.9 (the Kummer sequence), p. 53; Corollary 11.6, p. 80; the proof of
  Proposition 14.2, p. 90, which applies the Kummer sequence in the same way to curves over an
  algebraically closed field.
- The Stacks Project, Section 59.28 (Tag 03PK), <https://stacks.math.columbia.edu/tag/03PK>: Lemma
  59.28.1 (Tag 03PL), the exactness of the Kummer sequence on the étale site when $n$ is invertible,
  and the long exact cohomology sequence after it, which uses
  $H^1(S_{\mathrm{et}}, \mathbb{G}_m) = \operatorname{Pic}(S)$ (Theorem 59.24.1, Tag 03P8); and Lemma
  33.9.3 (Tag 0BUG), <https://stacks.math.columbia.edu/tag/0BUG>, on $H^0$ of the structure sheaf of a
  proper scheme over a field.
- J. S. Milne, *Étale Cohomology*, Princeton University Press, 1980: III 4.11, as cited by Milne,
  *Abelian Varieties*, p. 114 (not read).
- A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), X 3.1, as cited by Milne,
  *Abelian Varieties*, p. 114 (not read).
