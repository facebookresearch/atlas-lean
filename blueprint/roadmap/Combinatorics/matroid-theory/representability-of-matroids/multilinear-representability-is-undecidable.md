# Multilinear representability of matroids is undecidable over every field

For every field $F$, no algorithm decides whether a given finite matroid can be represented by an arrangement of equidimensional subspaces over $F$; the problem stays undecidable when the field is left unspecified.

Let $M$ range over finite matroids, given by their rank functions, and use the notion of a matroid [multilinear over a field](multilinear-matroids.md), that is, representable as a $c$-arrangement for some $c \ge 1$.

**Theorem (Kühne and Yashfe).** Fix a field $F$. The *multilinear representability problem over $F$*, which asks, given a matroid $M$, whether there is $c \ge 1$ such that $M$ is representable as a $c$-arrangement over $F$, is undecidable. This holds for every field $F$, and the problem remains undecidable when the field is unspecified (is $M$ multilinear over some field?) or is allowed to range over a given set of fields (Theorem 1.3 of arXiv:1912.06123v2).

Only the matroid is the input; the field is fixed in advance. By contrast, over an algebraically closed field, linear representability ($c = 1$) and, for each fixed $c$, representability as a $c$-arrangement can be decided by Gröbner basis computations, while linear representability over $\mathbb{Q}$ is equivalent to Hilbert's tenth problem over $\mathbb{Q}$, whose decidability is open. With the network coding constructions of El Rouayheb, Sprintson and Georghiades, the theorem implies that it is undecidable whether a network coding instance has a linear vector coding solution.

## Depends on

- [Matroids given by rank functions](matroids-given-by-rank-functions.md)
- [Multilinear matroids](multilinear-matroids.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Field](../../../Algebra/rings-and-fields/field.md)

## Proof depends on

None.

## Expansion

The proof reduces the uniform word problem for finite groups, undecidable by a theorem of Slobodskoi: given a finite presentation $\langle S \mid R \rangle$ and a word $w$, is $w$ mapped to the identity by every homomorphism to a finite group? From the presentation the source builds generalized Dowling geometries, matroids of rank three encoding the multiplication of the group (triangle matroids with a distinguished basis), and von Staudt constructions. A $c$-arrangement representation of such a matroid yields a representation of the group by invertible $c \times c$ matrices, and finite quotients in which $w$ survives yield representations of the matroids; the subtle point is the existence of fixed points of the matrix representations, which the source handles through weak $c$-representations (Theorem 4.6 of arXiv:1912.06123v2). A good expansion links Slobodskoi's undecidability of the uniform word problem for finite groups, which has no page.

## Sources

- L. Kühne and G. Yashfe, "Representability of matroids by $c$-arrangements is undecidable", *Israel Journal of Mathematics* 252 (2022), no. 1, 95–147, doi:10.1007/s11856-022-2345-z; read as arXiv:1912.06123v2, <https://arxiv.org/abs/1912.06123v2>: Problem 1.2, Theorem 1.3, Theorem 1.4 (Slobodskoi), Theorem 4.6 and the outline of the proof in Section 2, in the numbering of arXiv:1912.06123v2.
