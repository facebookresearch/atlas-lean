# The common multiple shape problem for sets of polyominoes is undecidable

No algorithm decides, for two finite sets of polyominoes, whether some region of positive area can be tiled both by copies of pieces of the first set and by copies of pieces of the second, even when all pieces are small.

A *polyomino* is a polygon obtained by joining one or more unit squares edge to edge; the pieces here are simple polyominoes (without holes). For a finite set $S$ of polyominoes let $\widehat S$ be the set of shapes that can be formed from copies of pieces of $S$, each piece usable any number of times. The *common multiple shape problem* asks, given finite sets $S_1$ and $S_2$ of polyominoes, whether $\widehat{S_1}\cap\widehat{S_2}$ contains a shape of positive area; such a shape is a *common multiple shape*. A set of polyominoes is *small* if its largest piece has $O(|S|^c)$ cells for a constant $c$.

**Theorem (Banbara, Minato, Ono and Uehara).** The common multiple shape problem is undecidable, already for two finite sets $S_1$ and $S_2$ of small polyominoes.

Conventions: the target shape is not part of the input and may have holes even when all pieces are simple. The case $|S_1|=|S_2|=1$ is the classical puzzle of polyform compatibility. The variant in which every piece of each set must be used exactly once (the shape logic puzzle) is decidable: the source shows it is strongly NP-complete for small polyominoes and polynomial when the number of pieces is constant. The source also derives that it is undecidable whether copies of a given finite set of small polyominoes form a rectangle.

## Depends on

- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

The proof goes through a jigsaw puzzle with square pieces whose edges carry colors $0,1,\dots,c$ and $\bar1,\dots,\bar c$: adjacent edges must carry complementary colors $i$ and $\bar i$, and exactly the boundary of the region carries color $0$. A fixed set of $11$ pieces tiles a region with boundary color $0$ iff the region is a rectangle of size at least $3\times3$ (Lemma 3), and from an instance of the Post correspondence problem one builds pieces that tile some region with boundary color $0$ iff the instance has a solution (Lemma 4): the top row spells the upper words, the bottom row the lower words, and colored paths match the index of each upper block to that of its lower block. Each colored square becomes a small polyomino by replacing each color by a zigzag edge pattern encoding it in binary, with $O((\log|C|)^2)$ cells. With $S_1$ from Lemma 3 and $S_2$ from Lemma 4, a common multiple shape exists iff the instance is solvable.

## Sources

- Mutsunori Banbara, Shin-ichi Minato, Hirotaka Ono and Ryuhei Uehara, "On the computational complexity of generalized common shape puzzles", in *SOFSEM 2024: Theory and Practice of Computer Science*, Lecture Notes in Computer Science, Springer, 2024, pp. 55–68, doi:[10.1007/978-3-031-52113-3_4](https://doi.org/10.1007/978-3-031-52113-3_4); read in arXiv:2305.10749v1, whose numbering is used here: Section 2 (polyominoes, small sets and the two puzzles), Observation 1 and Theorem 2 (the shape logic puzzle), and Section 4 (Lemmas 3 and 4, Theorem 5 and its proof outline, and the corollary on rectangles in the introduction).
