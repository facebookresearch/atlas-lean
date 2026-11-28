# HyperLTL satisfiability is Σ¹₁-complete

Whether a given HyperLTL sentence has a model, an arbitrary set of traces, is a $\Sigma^1_1$-complete problem. In particular it is undecidable, and the set of satisfiable sentences is neither recursively enumerable nor co-recursively enumerable.

**Theorem (Fortin, Kuijer, Totzke and Zimmermann).** Fix a finite set $AP$ of atomic propositions. The *satisfiability problem* for [HyperLTL](../hyperltl.md) asks, given a HyperLTL sentence $\varphi$ over $AP$ (a prenex formula with no free trace variables), whether there is a set $T \subseteq (2^{AP})^\omega$ of traces with $T \models \varphi$. Here $T$ ranges over all sets of traces, finite or infinite, with no finiteness, regularity or periodicity condition. This problem is $\Sigma^1_1$-complete: it lies in $\Sigma^1_1$, and it is $\Sigma^1_1$-hard (Theorem 3.1 of the source; hardness reduces the recurrent tiling problem for the positive quadrant). The empty set of traces is allowed as a model.

Here $\Sigma^1_1$ is the class of sets of the form $\{x \in \mathbb N \mid \exists f_0 \cdots \exists f_k\ \psi(x, f_0, \ldots, f_k)\}$, where the $f_i$ range over functions $\mathbb N \to \mathbb N$ and $\psi$ is a formula of arithmetic in the signature $(0, 1, +, \cdot, <)$ with arbitrary quantification over natural numbers only. A set is $\Sigma^1_1$-hard if every $\Sigma^1_1$ set many-one reduces to it by a computable function, and $\Sigma^1_1$-complete if it is moreover in $\Sigma^1_1$; the source's hardness proof is such a reduction from the recurrent tiling problem, which is $\Sigma^1_1$-complete. Since $\Sigma^1_1$ properly contains every level of the [arithmetical hierarchy](../../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md), a $\Sigma^1_1$-complete set is not arithmetical.

The same paper shows that the problem stays $\Sigma^1_1$-complete when the models are restricted to [sets of ultimately periodic traces](hyperltl-satisfiability-over-ultimately-periodic.md), while the restriction to finite sets of ultimately periodic traces is $\Sigma^0_1$-complete (Finkbeiner, Hahn and Hans, recalled after Theorem 3.1 of the source).

## Depends on

- [HyperLTL](../hyperltl.md)
- [The arithmetical class $\Sigma_n$](../../../../TheoryOfComputation/degrees-and-hierarchies/arithmetical-hierarchy/is-sigma.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)
- [Recognizability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-recognizable.md)
- [Co-recognizability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-co-recognizable.md)

## Proof depends on

None.

## Expansion

*Membership.* Every satisfiable HyperLTL sentence has a countable model (Finkbeiner and Zimmermann, STACS 2017). A countable model can therefore be coded by a set of natural numbers, its traces by numbers, and Skolem functions for the existential trace quantifiers by functions $\mathbb N \to \mathbb N$. Satisfiability then says: there exist a countable set of traces and Skolem functions such that every trace assignment consistent with them satisfies the quantifier-free LTL part. Checking an LTL formula on a fixed tuple of traces is arithmetical, so the whole statement is $\Sigma^1_1$ (Lemma 3.2).

*Hardness.* The proof reduces from the recurring tiling problem (Harel, 1985): given finitely many Wang tiles and a designated tile $\tau_0$, is there a tiling of the quadrant $\mathbb N \times \mathbb N$ in which $\tau_0$ occurs infinitely often in the first column? This problem is $\Sigma^1_1$-complete. In the reduction each column of the quadrant is a trace and each row is a time point; a designated proposition $x$ marks on each trace the time equal to its column index, and HyperLTL formulas force every column index to be represented, the horizontal constraints between consecutive columns and the vertical constraints along each trace, and infinitely many occurrences of $\tau_0$ on the column-$0$ trace (Lemma 3.3). A good expansion adds pages for the analytical hierarchy, its level $\Sigma^1_1$ and completeness under many-one reductions, for the countable-model property of HyperLTL (Finkbeiner and Zimmermann) and for the $\Sigma^1_1$-completeness of the recurring tiling problem (Harel).

## Sources

- M. Fortin, L. B. Kuijer, P. Totzke and M. Zimmermann, "HyperLTL Satisfiability Is Highly Undecidable, HyperCTL* is Even Harder", *Logical Methods in Computer Science* 21(1), 2025, article 3, <https://doi.org/10.46298/lmcs-21(1:3)2025>; numbers from arXiv:2303.16699v5, <https://arxiv.org/abs/2303.16699v5>: Section 2.3 (the classes $\Sigma^0_1$, $\Sigma^1_1$, $\Sigma^2_1$), Theorem 3.1, with Lemma 3.2 (membership) and Lemma 3.3 (hardness).
- D. Harel, "Recurring dominoes: making the highly undecidable highly understandable", *North-Holland Mathematics Studies* 102:51–71, 1985, <https://doi.org/10.1016/S0304-0208(08)73075-5>: the $\Sigma^1_1$-completeness of the recurring tiling problem used for the lower bound; not read directly here: this clause rests on its statement in the arXiv copy of the first source above (Section 1 and Lemma 3.3).
