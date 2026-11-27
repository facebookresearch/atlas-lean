# Representability of matroids over division rings is undecidable

No algorithm decides whether a given finite matroid is representable over some division ring, or over some division ring of a fixed characteristic, even for connected matroids of rank three; and there is a single division ring over which representability is undecidable.

Let $M$ range over finite matroids, given by their rank functions, with representations over division rings and skew-linear matroids as in [matroids and their representations](matroid-representations.md).

**Theorem (Kühne, Pendavingh and Yashfe).** The following problems are undecidable (Theorem 4.1 of arXiv:2012.07361v1):

1. given a matroid $M$, is $M$ skew-linear, that is, representable over some division ring?
2. for a fixed $p$ that is a prime or $0$: given a matroid $M$, is there a division ring of characteristic $p$ over which $M$ is representable?

Moreover, there is a division ring $D$ such that it is undecidable, given a matroid $M$, whether $M$ is representable over $D$.

Problems 1 and 2 remain undecidable when the input is restricted to connected matroids of rank $3$; Bérczi, Gehér, Imolay, Lovász, Padró and Schwarcz state this (Proposition 2.7 of arXiv:2507.10709v2), noting that the proof of Kühne, Pendavingh and Yashfe gives the rank-$3$ case, that loops may be deleted, and that every disconnected loopless rank-$3$ matroid is representable over every infinite field. By contrast, linear representability over some field, and over a fixed finite or algebraically closed field, is decidable, as the first source recalls. Representability over a division ring of characteristic in a given finite set is co-recursively enumerable (Corollary 5.17 of the second source).

## Depends on

- [Matroids and their representations over division rings, by subspaces and by random variables](matroid-representations.md)

## Proof depends on

- [Novikov–Boone theorem (unsolvability of the word problem)](../../../GroupTheory/presentations-and-decision-problems/word-problem-for-groups/novikov-unsolvable.md)

## Expansion

Macintyre showed that from a universal Horn sentence $H$ in the language of groups one can compute a universal Horn sentence $H'$ that is true in all division rings exactly when $H$ is true in all groups, and constructed for each characteristic a division ring $D_p$ that witnesses the falsity of $H'$ whenever possible. A universal Horn sentence is true in all groups exactly when the corresponding word is trivial in the corresponding finitely presented group, so by the unsolvability of the word problem the truth of Horn sentences in division rings (in all of them, in those of characteristic $p$, or in a suitable single one) is undecidable. Through von Staudt constructions, each Horn sentence yields finitely many matroids such that the sentence fails in a class of division rings exactly when one of them is representable over a member of the class (Lemma 4.2 of arXiv:2012.07361v1). A good expansion links Macintyre's theorem on Horn sentences in groups and division rings, which has no page.

## Sources

- L. Kühne, R. Pendavingh and G. Yashfe, "Von Staudt constructions for skew-linear and multilinear matroids", *Combinatorial Theory* 3 (2023), no. 1, article 16, doi:10.5070/C63160429; read as arXiv:2012.07361v1, <https://arxiv.org/abs/2012.07361v1>: Theorem 4.1, Lemma 4.2 and Section 4.1 (Macintyre's results), in the numbering of arXiv:2012.07361v1.
- K. Bérczi, B. Gehér, A. Imolay, L. Lovász, C. Padró and T. Schwarcz, "Interaction between skew-representability, tensor products, extension properties, and rank inequalities", in *Proceedings of the 2026 Annual ACM-SIAM Symposium on Discrete Algorithms (SODA)*, SIAM, 2026, pp. 328–354, doi:10.1137/1.9781611978971.15; read as arXiv:2507.10709v2, <https://arxiv.org/abs/2507.10709v2>: Proposition 2.7 and the paragraph before it, and Corollary 5.17, in the numbering of arXiv:2507.10709v2.
