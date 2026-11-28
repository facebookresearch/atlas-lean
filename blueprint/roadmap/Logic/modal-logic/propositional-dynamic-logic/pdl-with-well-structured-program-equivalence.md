# Variants of PDL that express well-structured program equivalence have Π¹₁-hard validity

Every variant of propositional dynamic logic that can express program composition, while-do loops and the fixed-point test "every halting run of p ends where it started" has a Π¹₁-hard validity problem, whether or not atomic programs are deterministic; in particular strict deterministic PDL with intersection is highly undecidable.

**Theorem (Goldblatt and Jackson).** In the relational semantics of [PDL programs](propositional-dynamic-logic-pdl/program.md), let $\mathrm{Fix}(p)$ be the proposition true at a state $a$ iff every computation of $p$ from $a$ ends in $a$, that is, $\mathrm{Fix}(p) = \{a \mid \forall b\, ((a, b) \in p \to a = b)\}$, and let $\mathrm{fix}(p) = \mathrm{Fix}(p) \wedge \langle p\rangle\mathsf T$. Fix any variation VPDL of PDL capable of expressing the usual connectives on propositions, program composition, while-do, the modal operators and $\mathrm{fix}$. Then:

1. the validity problem for VPDL is $\Pi^1_1$-hard, regardless of whether atomic programs are assumed to be deterministic or not (Theorem 4.1 of the source);
2. the set of VPDL propositions valid over finite relational models is not recursively enumerable, so VPDL has no axiomatization over finite models (Theorem 4.4).

*Strict deterministic PDL with intersection* (SDIPDL), with deterministic atomic programs, if-then-else, while-do and program intersection but no union or iteration, can express program equivalence $p \bowtie q$ (true at $a$ iff $p$ and $q$ relate $a$ to the same states), and hence $\mathrm{fix}(p)$ as $p \bowtie \mathsf{skip}$ together with $\langle p\rangle\mathsf T$; the source records the resulting high undecidability of SDIPDL as Corollary 4.2, settling a question left open in the Stanford Encyclopedia of Philosophy. PDL with program difference, and hence with program complementation, is also covered (Corollary 4.3). By contrast, strict deterministic PDL without intersection is PSPACE-complete, and nondeterministic PDL with intersection is decidable.

## Depends on

- [PDL programs](propositional-dynamic-logic-pdl/program.md)
- [PDL formulas](propositional-dynamic-logic-pdl/formula.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Recognizability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)

## Proof depends on

None.

## Expansion

The proof reduces a $\Sigma^1_1$-complete tiling problem: given a finite set of tiles with a distinguished subset of "neon" tiles, is there a tiling of the quadrant $\omega \times \omega$ with a fixed tile at $(0, 0)$ and infinitely many neon tiles on the diagonal? For a tile set a formula $\gamma = \alpha_0 \wedge \rho_1 \wedge \rho_2 \wedge \rho_3$ is built, with programs $N$ and $E$ for the two grid directions: $[x^*]\alpha$ is expressed as $[\mathsf{while}\ \alpha\ \mathsf{do}\ x]\mathsf F$, $\mathrm{fix}$ forces the squares of the grid to close, and $\rho_3 = [(N ; E)^*]\langle(N ; E)^*\rangle\mathit{neon}$ demands infinitely many neon tiles on the diagonal. The tile set has such a tiling iff $\gamma$ is satisfiable, iff it is satisfiable with deterministic (even injective) atomic programs; hence validity is $\Pi^1_1$-hard. Part 2 reduces the recursive inseparability of the tile sets that tile $\mathbb Z \times \mathbb Z$ periodically from those that tile nothing. A good expansion links the $\Sigma^1_1$-completeness of this recurrent tiling problem (Tiling Fact 1 of the source).

## Sources

- R. Goldblatt and M. Jackson, "Well-structured program equivalence is highly undecidable", *ACM Transactions on Computational Logic* 13(3):1–8, 2012, <https://doi.org/10.1145/2287718.2287726>; read as arXiv:1103.1433v1, <https://arxiv.org/abs/1103.1433v1>: Section 1, Section 2 (program equivalence and $\mathrm{Fix}$), Section 3 (Tiling Facts 1 and 2) and Section 4 (Theorem 4.1, Corollaries 4.2 and 4.3, Theorem 4.4).
