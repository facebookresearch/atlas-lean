# Emptiness of deterministic propositional while programs with graph loop is Π⁰₁-complete

Deciding whether a propositional while program with the graph loop operator denotes the empty relation in every deterministic relational model is $\Pi^0_1$-complete, over all models and over finite ones; without the loop operator the problem is decidable.

**Theorem.** The emptiness problem for [propositional while programs with graph loop](propositional-while-programs-with-graph-loop.md) on deterministic valuations satisfying the test hypotheses is $\Pi^0_1$-complete. The same holds when only valuations over finite sets are considered: the set of $\mathrm{PWP}_{\circlearrowleft}$ terms $t$ with $\mathrm{DREL}^{\mathrm{fin}} \models t \le 0$ is $\Pi^0_1$-complete as well.

The proof adapts a reduction of Goldblatt and Jackson (ACM TOCL 2012), as the source states.

## Depends on

- [Propositional while programs with graph loop](propositional-while-programs-with-graph-loop.md)
- [The arithmetical class $\Pi_n$](../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-pi.md)

## Proof depends on

None.

## Expansion

*Upper bound.* The class of deterministic valuations satisfying the test hypotheses is closed under submodels, and the source's general upper bound for such classes places emptiness in $\Pi^0_1$: a non-empty term is witnessed by a finite model, so non-emptiness is recursively enumerable.

*Hardness.* The reduction is from the complement of the *periodic domino problem*: given a domino system $\langle C, H, V \rangle$ (colors with horizontal and vertical adjacency constraints), is there a periodic tiling of $\mathbb Z^2$? That problem is $\Sigma^0_1$-complete (Berger; Gurevich and Koryakov). Following Goldblatt and Jackson's undecidability proof for strict deterministic PDL with intersection, four actions $E, N, W, S$ describe a finite torus-shaped grid, and tests color its points. The hypotheses that the grid closes up and that each point satisfies the domino constraints have the form $1 \le t$; the new ingredient is a *hypothesis elimination using graph loops*, which turns such a hypothesis into a transformation $\mathrm{Tr}_t$ of the program itself. The resulting deterministic $\mathrm{PWP}_{\circlearrowleft}$ term is empty in every deterministic model iff the domino system has no periodic tiling. The source draws two corollaries. Validity of formulas $[t]\bot$, for $\mathrm{PWP}_{\circlearrowleft}$ terms $t$ (which contain no modal operators), is $\Pi^0_1$-complete in strict deterministic PDL with intersection. The equational theory of the positive calculus of relations with transitive closure and the difference constant is also $\Pi^0_1$-complete.

Without the graph loop the problem is decidable: emptiness is an equation of guarded Kleene algebra with tests, whose equational theory on deterministic models coincides with that on all relational models and is decidable.

## Sources

- Yoshiki Nakamura, "Undecidability of the Positive Calculus of Relations with Transitive Closure and Difference: Hypothesis Elimination Using Graph Loops", in *Relational and Algebraic Methods in Computer Science (RAMiCS 2024)*, Lecture Notes in Computer Science, Springer, 2024, pp. 207–224, <https://doi.org/10.1007/978-3-031-68279-7_13>, which proves this theorem and the result on the positive calculus of relations; read as the extended version arXiv:2504.20415v2, "Undecidability of the Emptiness Problem of Deterministic Propositional While Programs with Graph Loop: Hypothesis Elimination Using Loops", <https://arxiv.org/abs/2504.20415v2>: the main theorem of Section 6 and its proof, and the section "Differences from the Conference Version" in Section 1 of that version, which says the conference version already proved both results.
