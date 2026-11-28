# Flatness and étaleness criteria for homomorphisms of group schemes

This node is still to be broken down: the statements are precise, but their proofs are not.

Let $S$ be a scheme. The targets are:

1. (Fibrewise criterion of flatness.) Let $X$ and $Y$ be $S$-schemes locally of finite presentation,
   $f \colon X \to Y$ a morphism over $S$, $x \in X$, $y = f(x)$ and $s \in S$ the image of $x$.
   Then $X$ is flat over $S$ at $x$ and $f_s \colon X_s \to Y_s$ is flat at $x$ if and only if $Y$
   is flat over $S$ at $y$ and $f$ is flat at $x$. In particular, if $X$ and $Y$ are flat over $S$,
   then $f$ is flat if and only if $f_s$ is flat for every $s \in S$.
2. (Étaleness through the fibres.) A morphism $f \colon X \to Y$ locally of finite presentation is
   étale at a point $x$ if and only if it is flat at $x$ and the fibre of $f$ over $f(x)$ is étale
   at $x$ over $\kappa(f(x))$. Consequently, if $X$ and $Y$ are locally of finite presentation over
   $S$ and $f$ is a flat morphism over $S$, then $f$ is étale at a point $x$ of a fibre $X_s$ if and
   only if $f_s$ is.
3. (Group schemes over a field.) Let $k$ be a field and $f \colon G \to H$ a homomorphism of group
   schemes of finite type over $k$. If $f$ is surjective and $H$ is smooth, then $f$ is flat. If $G$
   and $H$ are smooth, then $f$ is étale if and only if its differential $\operatorname{Lie}(G) \to
   \operatorname{Lie}(H)$ at the identity is an isomorphism. For morphisms $\alpha, \beta \colon G
   \to H$ of $k$-schemes preserving the identity, the product $\alpha \beta = m_H \circ (\alpha,
   \beta)$ has differential $d\alpha_e + d\beta_e$ at the identity, as the differential of the
   multiplication $m_H$ at $(e, e)$ is the addition of $\operatorname{Lie}(H)$; in particular
   multiplication by $n$ on a commutative $G$ has differential $n$.

The page on [isogenies of abelian schemes](isogenies-of-abelian-schemes.md) uses them as follows. By
3 on the fibres and 1 over $S$, a surjective homomorphism of abelian schemes and multiplication by
$n$ are flat; by 3, $n_A$ is étale on a fibre $A_s$ exactly when $n$ is invertible in $k(s)$ or
$A_s$ has dimension $0$, and 2 passes from the fibres to $S$.

## Depends on

- [Flat morphisms of schemes](../schemes-and-morphisms/flat-morphism-of-schemes.md), for the flat
  morphisms of the statement
- [Smooth morphisms of schemes](../schemes-and-morphisms/smooth-morphisms/smooth-morphism-of-schemes.md),
  for its smooth morphisms
- [Étale morphisms of schemes](../schemes-and-morphisms/etale-morphism-of-schemes.md), for its étale
  morphisms

## Proof depends on

Its proof uses the inputs listed under Expansion.

## Expansion

A good expansion has pages for: the local criterion of flatness and its fibrewise form (EGA IV₃,
§11.3, Théorème (11.3.10); Stacks Project, Section 37.16); the description of étale morphisms
through flatness and their fibres (Stacks Project, Section 29.37, Lemma 29.37.15, Tag 02GU); and,
over a field, the flatness of a surjective homomorphism onto a smooth group scheme, through generic
flatness and translations, and the Jacobian criterion for étaleness at the identity, carried to
every point by translations.

A good expansion also states and links:

- group schemes over a base (Stacks Project, Section 39.4), with their Lie algebras, for the
  statement

## Sources

- A. Grothendieck, avec la collaboration de J. Dieudonné, *Éléments de géométrie algébrique IV.
  Étude locale des schémas et des morphismes de schémas, troisième partie*, Publications
  Mathématiques de l'IHÉS 28 (1966): Théorème (11.3.10) (critère de platitude par fibres), in the
  case 2° (morphisms locally of finite presentation), with $\mathcal{F} = \mathcal{O}_X$.
- The Stacks Project, Theorem 37.16.2, <https://stacks.math.columbia.edu/tag/039C> (critère de
  platitude par fibres), and Lemma 29.37.15, <https://stacks.math.columbia.edu/tag/02GU> (étaleness
  at a point through flatness and the fibre).
- D. Robert, *Theory of abelian varieties and their moduli spaces*, draft book (version of 7 March
  2023), <https://www.math.u-bordeaux.fr/~damienrobert/pro/publications/books/avtheory.pdf>: the
  proof of Proposition 2.3.15, p. 17, which cites his Proposition B.1.4 for the flatness on the
  fibres of a surjective homomorphism onto a smooth group scheme, and Mumford–Fogarty–Kirwan, Lemma
  6.12.
- J. S. Milne, *Abelian Varieties*, course notes, version 2.00 (2008),
  <https://www.jmilne.org/math/CourseNotes/AV.pdf>: the proof of Theorem I.7.2, p. 33 (the
  differential of $n_A$, its additivity and étaleness by homogeneity).
