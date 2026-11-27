# The positive calculus of relations with reflexive transitive closure and difference is undecidable

The equational theory of binary relations in the positive calculus of relations, extended with reflexive transitive closure and the difference constant (the complement of the identity), is undecidable.

**Terms.** Terms are built from variables (relation letters) and the constants $1$ (identity), $0$ (empty relation) and $\top$ (full relation) by composition $t \cdot u$, union $t \cup u$, intersection $t \cap u$ and converse $t^\smile$; these are the terms of the positive calculus of relations $\mathrm{PCoR}$, a fragment of the [calculus of relations](calculus-of-relations.md). $\mathrm{PCoR}_{\{*, \bar{1}\}}$ adds reflexive transitive closure $t^*$ and the *difference constant* $\bar{1}$. In a relational model, a nonempty set $W$ with a binary relation on $W$ for each variable, terms denote binary relations on $W$: $1$ is the identity, $\bar{1} = W^2 \setminus 1$, the operations are interpreted as the operations on relations, and $t^*$ is the reflexive transitive closure of $t$. An equation $t = u$ belongs to the *equational theory* if both sides denote the same relation in every relational model.

**Theorem (Nakamura).** The equational theory of $\mathrm{PCoR}_{\{*, \bar{1}\}}$ is undecidable.

The equational theory of $\mathrm{PCoR}$ is decidable (Andréka and Bredikhin), and it remains decidable with reflexive transitive closure added, so the difference constant is what makes the theory undecidable. The extended version of the source shows that the theory is $\Pi^0_1$-complete, already for inclusions $t \leq u$ in which $t$ uses composition, union, reflexive transitive closure and the loop operator $t \cap 1$, and $u$ uses composition, union, the loop operator and $\bar{1}$ (Corollary 8.2 of arXiv:2504.20415v2, there with numbering of that version).

## Depends on

- [Calculus of relations](calculus-of-relations.md)

## Proof depends on

None.

## Expansion

The proof eliminates hypotheses using graph loops. Undecidability is first shown for inclusions under hypotheses that describe a finite torus-shaped grid, following Goldblatt and Jackson's reduction for strict deterministic propositional dynamic logic with intersection, by reduction from the periodic domino problem. The hypotheses (that the grid closes up and that the edge relations are partial functions inverse to each other) are then eliminated: in the presence of the difference constant, an equation under such hypotheses is equivalent to a single equation in which the hypotheses are expressed with loops $t \cap 1$.

## Sources

- Y. Nakamura, "Undecidability of the positive calculus of relations with transitive closure and difference: hypothesis elimination using graph loops", in *Relational and Algebraic Methods in Computer Science (RAMiCS 2024)*, Lecture Notes in Computer Science 14787, Springer, 2024, pp. 207–224, doi:10.1007/978-3-031-68279-7_13; read as its extended version arXiv:2504.20415v2, <https://arxiv.org/abs/2504.20415v2> ("Undecidability of the emptiness problem of deterministic propositional while programs with graph loop: hypothesis elimination using loops"): Section 2 (syntax and semantics of $\mathrm{PCoR}$ with reflexive transitive closure and complements), the introduction and its comparison with the conference version, and Corollary 8.2 with its proof.
