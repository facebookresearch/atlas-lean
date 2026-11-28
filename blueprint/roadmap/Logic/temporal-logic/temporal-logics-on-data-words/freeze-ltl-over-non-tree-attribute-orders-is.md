# Freeze LTL over attributes that are not a tree-quasi-ordering is undecidable

Satisfiability of freeze LTL with quasi-ordered attributes is $\Sigma^0_1$-complete, hence undecidable, as soon as the attribute ordering is not a tree-quasi-ordering; tree-quasi-orderings, conversely, give decidable satisfiability.

**Theorem (Decker and Thoma).** Let $(A, \sqsubseteq)$ be a quasi-ordered set of attributes that is not a tree-quasi-ordering. Then the satisfiability problem of [$\mathrm{LTL}^{\downarrow}_A$](freeze-ltl-with-quasi-ordered-attributes.md) over $A$-attributed data words is $\Sigma^0_1$-complete.

So satisfiability of $\mathrm{LTL}^{\downarrow}_A$ is decidable iff $(A, \sqsubseteq)$ is a tree-quasi-ordering. The decidable side is shown in the same paper, where satisfiability for tree-quasi-orderings is complete for the fast-growing complexity class $\mathbf{F}_{\varepsilon_0}$. Undecidability already needs only three attributes $x \sqsubseteq z \sqsupseteq y$ with $x$, $y$ incomparable, and no past-time operators.

## Depends on

- [Freeze LTL with quasi-ordered attributes](freeze-ltl-with-quasi-ordered-attributes.md)
- [The arithmetical class $\Sigma_n$](../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

Membership in $\Sigma^0_1$ holds because data words are finite and only the equality type of their data matters, so satisfying words can be enumerated. For hardness, the proof adapts the reduction of Bojańczyk, David, Muscholl, Schwentick and Segoufin, who showed undecidability of two-variable first-order logic on data words with two class relations by encoding Post's correspondence problem. Freezing $z$ stores the pair of values of $x$ and $y$ as a set, which together with independent checks on $x$ and $y$ suffices to link positions of the two halves of a candidate solution; ideas of Demri, Figueira and Praveen remove the past-time operators. The argument extends to every quasi-ordering containing such a triple.

## Sources

- N. Decker and D. Thoma, "On freeze LTL with ordered attributes", in *Foundations of Software Science and Computation Structures (FoSSaCS 2016)*, Lecture Notes in Computer Science 9634, Springer, 2016, pp. 269–284, doi:10.1007/978-3-662-49630-5_16; read as arXiv:1504.06355v2 (extended version), <https://arxiv.org/abs/1504.06355v2>: the theorem "Undecidability" (label thm:undecidability) in the section "Semantics and Undecidability of LTL↓qo", its proof in the appendix (Lemma lem:qo-undecidable), and the complexity results for tree-quasi-orderings.
