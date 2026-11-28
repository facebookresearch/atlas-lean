# Flat folding of a fixed infinite crease pattern with boundary constraints is coRE-complete

There is one fixed tame infinite crease pattern on a square of paper such that deciding whether it can be flat-folded consistently with a given finite set of folding decisions at its boundary is coRE-complete, hence undecidable. This holds for labeled and for unlabeled creases.

**Theorem (Eppstein).** There exists a fixed tame crease pattern $P$ on an open square of origami paper (with labeled creases, and also one with unlabeled creases) such that the following problem is undecidable and $\mathsf{coRE}$-complete: given a finite set $F$ of decisions about how to fold creases on the boundary of $P$, can $P$ be flat-folded consistently with $F$?

The crease pattern is fixed; only the finite boundary specification $F$ is the input: a finite list of above–below relations between the layers of specified folds at the boundary of $P$ (the source uses them to fix the input tape of a universal Turing machine and to mark the top rectangle of the tiling as active). $P$ consists of scaled copies of one finite crease pattern placed in the rectangles of a binary tiling of the square, so it has a finite description.

## Depends on

- [Flat foldings of crease patterns](flat-foldings-of-crease-patterns.md)
- [The arithmetical class $\Pi_n$](../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Co-recognizability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-co-recognizable.md)

## Proof depends on

- [Halting is undecidable](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

Fix a universal Turing machine $\mathcal{U}$ that directly simulates other machines on a semi-infinite tape delimited by two active tape terminators; its halting set is RE-complete. Gadgets from the NP-hardness proof of flat foldability (Akitaya et al.) implement Boolean circuits, with each wire a pleat whose two foldings encode a bit. The binary tiling of the square provides, at every scale, rectangles in which a fixed circuit computes one tape cell at one time step from its neighbors, so the folding of the whole pattern simulates the space-time diagram of $\mathcal{U}$. The decisions $F$ fix the input tape and activate the root rectangle; a "halt gate" makes folding fail at the cell and time where $\mathcal{U}$ halts. Hence $P$ folds consistently with $F$ exactly when $\mathcal{U}$ does not halt on the encoded input, using tameness and the reduction of flat foldability to finite regions to build a global folding from a non-halting run. A good expansion links pages for the pleat and circuit gadgets of Akitaya et al., for the width relation at junctions of three variable gadgets that lets the scaled gadgets of neighbouring rectangles of the binary tiling connect (Lemma 19 of the source), and for the reduction of flat foldability of a tame crease pattern to its nearby regions (Lemma 17).

## Sources

- David Eppstein, "Computational Complexities of Folding", Journal of Information Processing 33, pp. 954–973, 2025, <https://doi.org/10.2197/ipsjjip.33.954>; read in arXiv:2410.07666v1, <https://arxiv.org/abs/2410.07666v1>: Theorem 6 and Section 6 ("Infinite crease patterns"), in the numbering of that version.
