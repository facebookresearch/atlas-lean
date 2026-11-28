# Formation, equivalence and duality of two-counter session types are undecidable

For session types given by equations with two natural-number parameters, no algorithm decides whether a type identifier defines a type, whether two types are equivalent, or whether two types are dual. All three problems are decidable for recursive, one-counter and pushdown session types.

**Theorem (Gay, Poças and Vasconcelos).** For [two-counter session types](two-counter-session-types.md) the following problems are undecidable, where the input is a finite system of 2-counter equations together with type identifiers $X\langle n, n'\rangle$ (numerals $n, n'$):

- type formation: does $T\ \mathsf{type}_2$ hold?
- type equivalence: does $T \simeq_2 U$ hold?
- type duality: does $T \perp_2 U$ hold?

The boundary is sharp in the source's hierarchy. Contractiveness of recursive, one-counter and pushdown systems is decidable in polynomial time, and so are type formation for these three classes (Theorems 9 and 10); type equivalence and type duality are decidable for them (Theorems 11 and 12), equivalence of pushdown types through the decidability of equivalence of deterministic pushdown automata.

## Depends on

- [Two-counter session types](two-counter-session-types.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting is undecidable](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)
- [Two-counter machines are universal](../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

**Formation.** Start from the problem whether a one-tape Turing machine started on the empty tape reaches a given state $q$. The construction of Hopcroft and Ullman turns the machine into a two-counter automaton with an initial configuration $c_0$ and a state $q'$ that is reachable from $c_0$ by $\varepsilon$-moves exactly when the machine reaches $q$. Translate the automaton into a system of 2-counter equations, replacing the equations for $q'$ by $X_{q'}\langle N, M\rangle \doteq \mathsf{end}$. For the identifier $T$ of $c_0$, $T\ \mathsf{type}_2$ holds iff $T$ is contractive iff $q'$ is reachable from $c_0$ by $\varepsilon$-moves iff the machine reaches $q$.

**Equivalence.** Equivalence of identifiers requires contractiveness, so the previous reduction already applies. Independently, for decidable $E, F \subseteq \mathbb{N}$ let $T_E = \sharp_0 \mathsf{end}.\sharp_1 \mathsf{end}.\sharp_2 \mathsf{end} \cdots$ with $\sharp_n = ?$ if $n \in E$ and $!$ otherwise; both are 2-counter types because their trace languages are decidable, and $E = F$ iff $T_E \simeq_2 T_F$, while equality of decidable (even context-free) languages is undecidable.

**Duality.** $T \perp_2 U$ iff $\overline{T} \simeq_2 U$ for the dual $\overline{T}$, which is computable from $T$.

A good expansion links the reduction from Turing machines to two-counter automata (the universality page above states the halting form, while the proof uses reachability of a state by $\varepsilon$-moves), the correspondence between 2-counter types and decidable trace languages (Theorem 5 of the source) and the computability of the dual type (Lemma 8 of the source).

## Sources

- Simon J. Gay, Diogo Poças and Vasco T. Vasconcelos, "The Different Shades of Infinite Session Types", Foundations of Software Science and Computation Structures (FoSSaCS 2022), Lecture Notes in Computer Science 13242, pp. 347–367, Springer, 2022, <https://doi.org/10.1007/978-3-030-99253-8_18>. Read in arXiv:2201.08275v1, <https://arxiv.org/abs/2201.08275v1>; Theorem 13 (undecidability results) with its proof in Section 8, Theorems 9 to 12 (decidable cases), Theorem 5, Lemma 7 (contractiveness and loop-free automata) and Lemma 8 (dual types), numbering of arXiv:2201.08275v1.
