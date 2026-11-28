# The étale fundamental group and first étale cohomology with finite coefficients

This node is still to be broken down: the statements are precise, but their proofs are not.

Let $X$ be a connected scheme and $\bar x$ a geometric point of $X$, with values in an algebraically
closed field. For a finite étale covering $Y \to X$ write $F(Y) = Y_{\bar x}$ for its geometric fibre
over $\bar x$, the set of lifts of $\bar x$ to $Y$; this is the fibre functor $F$ on finite étale
coverings of $X$. The étale fundamental group $\pi_1(X, \bar x)$ is the group of automorphisms of $F$,
the [arithmetic fundamental group](../not-yet-classified/etale-fibre-frobenius/arithmetic-fundamental-group.md),
with the profinite topology given by its action on the finite sets $F(Y)$; it acts continuously on the
left on each $F(Y)$.

1. (Classification of coverings.) The functor $Y \mapsto F(Y)$ is an equivalence from the category
   of finite étale coverings of $X$ to the category of finite discrete sets with a continuous action
   of $\pi_1(X, \bar x)$. In particular, since an equivalence preserves finite coproducts, a nonempty
   covering $Y$ is connected exactly when $\pi_1(X, \bar x)$ acts transitively on $F(Y)$.
2. (First cohomology.) Let $M$ be a finite abelian group, regarded as a constant sheaf on the étale
   site $X_{\mathrm{et}}$. There is an isomorphism
   $H^1(X_{\mathrm{et}}, M) \cong \operatorname{Hom}_{\mathrm{cont}}(\pi_1(X, \bar x), M)$, natural in
   $M$, which sends the class of an $M$-torsor $P \to X$, a finite étale covering with an action of
   $M$ over $X$ that is simply transitive on every geometric fibre, to the homomorphism $\rho$ with
   $\gamma p = p \cdot \rho(\gamma)$ for all $\gamma \in \pi_1(X, \bar x)$ and $p \in F(P)$; the
   element $\rho(\gamma)$ does not depend on $p$, since the two actions on $F(P)$ commute and $M$ is
   commutative.

So the continuous homomorphisms $\pi_1(X, \bar x) \to M$ classify the Galois coverings of $X$ with
group $M$, the form in which Milne uses 2 for abelian varieties and Jacobians.

## Expansion

This node is still to be broken down. A good expansion states and links:

- the identification of $\pi_1(X, \bar x)$ with Milne's $\varprojlim_i \operatorname{Aut}_X(X_i)$, the
  limit over a cofinal system of connected finite étale Galois coverings $X_i \to X$ pointed over
  $\bar x$, and the equivalence of 1 (the Stacks Project, Theorem 58.6.2, which states it for
  $\pi_1(X, \bar x) = \operatorname{Aut}(F_{\bar x})$; Milne, *Lectures on Étale Cohomology*, Theorem
  3.1, a survey statement whose proofs are in the references at the end of his §3);
- the identification of $H^1(X_{\mathrm{et}}, G)$ with Čech cohomology and the bijection between Čech
  classes and isomorphism classes of torsors (the same notes, the opening of §11 and Proposition
  11.1);
- the representability of a torsor under a finite constant group by a finite étale covering of $X$;
- the passage from torsors under $M$ to homomorphisms $\pi_1(X, \bar x) \to M$ through 1 (the same
  notes, Example 11.3), and the naturality of 2 in $M$ and under morphisms of pointed connected
  schemes.

## Depends on

- [Étale morphisms of schemes](../schemes-and-morphisms/etale-morphism-of-schemes.md), for finite
  étale coverings
- [Arithmetic Fundamental Group](../not-yet-classified/etale-fibre-frobenius/arithmetic-fundamental-group.md),
  for $\pi_1(X, \bar x)$ as the automorphism group of the fibre functor
- [Fibre Automorphism Topology](../not-yet-classified/etale-fibre-frobenius/fibre-automorphism-topology.md),
  for the profinite topology on $\pi_1(X, \bar x)$

## Sources

- J. S. Milne, *Lectures on Étale Cohomology*, course notes, version 2.21 (2013), <https://www.jmilne.org/math/CourseNotes/LEC.pdf>: §3, the definition of $\pi_1(X, \bar x)$ as $\varprojlim_i \operatorname{Aut}_X(X_i)$ and Theorem 3.1, p. 27; §11, its opening
  paragraph, p. 76, Proposition 11.1, p. 77, and Example 11.3, p. 78 (for a connected $X$ and a finite
  group $G$, a canonical isomorphism
  $H^1(X_{\mathrm{et}}, G) \cong \operatorname{Hom}_{\mathrm{conts}}(\pi_1(X, \bar x), G)$).
- The Stacks Project, Section 58.6 (Tag 0BQ8), <https://stacks.math.columbia.edu/tag/0BQ8>:
  Definition 58.6.1 (Tag 0BNC), $\pi_1(X, \bar x) = \operatorname{Aut}(F_{\bar x})$ for a connected
  scheme $X$, with the profinite topology of Lemma 58.3.1 (Tag 0BMR), and Theorem 58.6.2 (Tag 0BND),
  the equivalence between finite étale coverings of $X$ and finite $\pi_1(X, \bar x)$-sets.
- J. S. Milne, *Abelian Varieties*, course notes, version 2.00 (2008), <https://www.jmilne.org/math/CourseNotes/AV.pdf>: Chapter III, §9, its first paragraph, p. 113 (for a finite abelian group $M$, the
  continuous homomorphisms $\pi_1(V, P) \to M$ classify the Galois coverings of $V$ with group $M$),
  and the proof of Corollary 9.6, p. 115, which uses
  $H^1(V_{\mathrm{et}}, \mathbb{Z}/n\mathbb{Z}) = \operatorname{Hom}(\pi_1(V, P), \mathbb{Z}/n\mathbb{Z})$.
- J. S. Milne, *Étale Cohomology*, Princeton University Press, 1980: I §5 and III §4, as cited by
  Milne, *Abelian Varieties*, pp. 113 and 115 (not read).
