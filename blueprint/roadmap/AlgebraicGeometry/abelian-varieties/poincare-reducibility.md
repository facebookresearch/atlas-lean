# Poincaré's complete reducibility theorem

Let $A$ be an [abelian variety](abelian-scheme.md) over a perfect field $k$. An abelian variety is
simple if its only abelian subvarieties are $0$ and itself. Then there are simple abelian
subvarieties $A_1, \dots, A_n$ of $A$ such that the addition map

$$A_1 \times \dots \times A_n \to A, \qquad (a_1, \dots, a_n) \mapsto a_1 + \dots + a_n,$$

is an [isogeny](isogenies-of-abelian-schemes.md). Grouping isogenous factors, $A$ is isogenous to a
product $\prod_{i=1}^t B_i^{r_i}$ of powers of simple abelian varieties $B_i$ that are pairwise
non-isogenous.

Milne proves the first statement by induction from the case of one abelian subvariety $B$, $0 \ne B
\ne A$: for an ample invertible sheaf $L$ on $A$ and the inclusion $\imath \colon B \hookrightarrow
A$, the identity component $B'$ of the kernel of $\imath^\vee \circ \phi_L \colon A \to B^\vee$ meets
$B$ in a finite group, and $B \times B' \to A$, $(b, b') \mapsto b + b'$, is an isogeny. In his course
notes he remarks that the argument that $B'$ is an abelian variety requires a further proof when $k$
is not perfect; in the revised version of his article *Abelian varieties* he takes $B'$ to be the
reduced subscheme of that identity component, which is an abelian variety when $k$ is perfect, and
proves this for an imperfect field in lemmas after Proposition 12.1. The statement here is the case
of a perfect field, which covers the use of Gaudron and Rémond, over fields of characteristic zero.

## Expansion

This node is still to be broken down. A good expansion states and links:

- the inequality $\dim B' \ge \dim A - \dim B$ for the kernel of a homomorphism (Milne's notes, AG
  10.9, as cited there);
- the finiteness of the kernel of $\phi_{L|_B} = \imath^\vee \circ \phi_L \circ \imath$ for the ample
  sheaf $L|_B$;
- the fact that over a perfect field the reduced identity component of the kernel of a homomorphism
  of abelian varieties is an abelian variety;
- the induction on the dimension, and the grouping of isogenous factors.

## Depends on

- [Abelian scheme](abelian-scheme.md), for abelian varieties over $k$
- [Isogenies of abelian schemes](isogenies-of-abelian-schemes.md)

## Proof depends on

- [Abelian varieties are projective](abelian-varieties-are-projective.md), for an ample invertible
  sheaf $L$ on $A$
- [Dual abelian variety](dual-abelian-variety.md), for $\phi_L$, which is an isogeny for ample $L$,
  and the dual $\imath^\vee$ of the inclusion

## Sources

- J. S. Milne, *Abelian Varieties*, course notes, version 2.00 (2008),
  <https://www.jmilne.org/math/CourseNotes/AV.pdf>: Chapter I, §10, Proposition 10.1 with its proof
  and footnote 10, p. 42, and the decomposition $A \sim A_1^{n_1} \times \dots \times A_r^{n_r}$,
  p. 43.
- J. S. Milne, "Abelian varieties", in *Arithmetic Geometry* (Storrs, 1984), Springer, 1986,
  103–150; revised version of 2 January 2022, <https://www.jmilne.org/math/xnotes/AVs.pdf>: §12,
  Proposition 12.1 with its proof and the lemmas after it, pp. 19–20, and the decomposition of an
  abelian variety up to isogeny into powers of nonisogenous simple abelian varieties, p. 20 (the
  numbering of the revised version is that of the published article).
- É. Gaudron and G. Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014), 2057–2108,
  <https://doi.org/10.1215/00127094-2782528>: §9, p. 2097, where the decomposition of $A$ over $K$
  is taken from the complete reducibility theorem.
