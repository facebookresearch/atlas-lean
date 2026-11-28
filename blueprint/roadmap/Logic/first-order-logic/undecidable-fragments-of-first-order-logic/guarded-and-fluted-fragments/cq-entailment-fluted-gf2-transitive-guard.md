# Query entailment for fluted two-variable guarded logic with a transitive guard is undecidable

Whether a sentence of the fluted two-variable guarded fragment with a single transitive guard entails a conjunctive query is undecidable, over all models and over finite models, whereas satisfiability of the guarded fragment with regular guards is decidable.

**Setting (Bednarczyk and Kieroński).** Signatures are relational, without equality or constants. In the *guarded fragment* $\mathrm{GF}$ of first-order logic all quantification has the form $\forall \bar x\,(\alpha \to \psi)$ or $\exists \bar x\,(\alpha \wedge \psi)$, where the *guard* $\alpha$ is an atom containing all variables of $\bar x$ and all free variables of $\psi$. Its *two-variable* fragment $\mathrm{GF}^2$ uses only $x_1, x_2$ (requantification allowed), and a formula is *fluted* if, written so that the $i$-th quantifier on each branch binds $x_i$, every atom in the scope of the quantifier binding $x_n$ (but not $x_{n+1}$) has as arguments a suffix of $x_1, \dots, x_n$. A *transitive guard* is a binary predicate interpreted as a transitive relation and allowed to occur only as a guard; the logic $\mathrm{RGF}$ allows more general regular path programs as guards. A *conjunctive query* (CQ) is an existentially quantified conjunction of atoms ([answers of a conjunctive query](../../../../ComputerScience/databases/conjunctive-queries/answers-of-a-conjunctive-query.md)). The *(finite) entailment problem* asks, given a sentence $\varphi$ and a CQ $q$, whether every (finite) model of $\varphi$ satisfies $q$.

**Theorem (Bednarczyk and Kieroński).** Both the finite and the general CQ entailment problems are undecidable for $\mathrm{RGF}$, already for its fluted two-variable fragment with a single transitive guard (Theorem 5.4 of arXiv:2509.09218v1).

The reduction uses one fixed CQ with four variables. In description-logic terms, finite and general CQ entailment are undecidable for TBoxes $\mathcal{T} \cup \{\mathsf{tr}(p),\ p \subseteq h \cup \bar h\}$ with $\mathcal{T}$ an $\mathcal{ALC}^{\cap_\top}$-TBox, even for queries not mentioning the transitive role $p$ (Corollary 5.5). This strengthens the undecidability of UCQ entailment over $\mathrm{GF}^2$ with transitive guards (Gottlob, Pieris and Tendera) to fluted formulas, a single CQ and the finite case. By contrast, satisfiability of $\mathrm{RGF}$ is 2EXPTIME-complete (Theorem 4.6 of the source), and entailment of acyclic queries reduces to satisfiability.

## Depends on

- [Fluted fragment](fluted-fragment.md)
- [Two-variable guarded fragment](two-variable-guarded-fragment.md)
- [Answers of a conjunctive query](../../../../ComputerScience/databases/conjunctive-queries/answers-of-a-conjunctive-query.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof axiomatizes *snakes*, triangular grid-like structures over unary predicates for even columns, the bottom row and rows near the top, binary horizontal and vertical successor relations $H$ and $V$ (the direction of $V$ alternating between columns), and a transitive path relation $P$ used as the only transitive guard. A formula $\varphi_{\mathbb{S}}$ in the fluted two-variable guarded fragment with guard $P$, conjoined with the negation of the grid-closing query $\exists x\,y\,z\,t\,(V(x,y) \wedge H(y,z) \wedge V(z,t) \wedge \bar H(x,t))$, forces every model to contain an injective, type-preserving image of the infinite snake, and every finite model one of a finite snake (Lemma 5.3). Adding unary tile predicates reduces the tiling problem for the octant $\{(n, m) : m \le n\}$, and its finite variant, to non-entailment. A complete expansion links a page for the undecidability of the infinite and finite octant tiling problems, which has none on main.

## Sources

- B. Bednarczyk and E. Kieroński, "Guarded Fragments Meet Dynamic Logic: The Story of Regular Guards", in *Proceedings of the 22nd International Conference on Principles of Knowledge Representation and Reasoning (KR 2025)*, 2025, pp. 89–99, doi:[10.24963/kr.2025/9](https://doi.org/10.24963/kr.2025/9); read as arXiv:2509.09218v1 ([arXiv](https://arxiv.org/abs/2509.09218v1)), the extended version, whose numbering is used (counters within section): the definitions of Sections 2 and 3, Theorem 4.6, and Definition 5.1, Lemma 5.3, Theorem 5.4 and Corollary 5.5 of Section 5.
