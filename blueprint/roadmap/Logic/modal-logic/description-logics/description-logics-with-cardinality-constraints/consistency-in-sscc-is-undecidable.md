# Consistency in SSCC is undecidable

Adding transitivity axioms to the description logic ALCSCC makes TBox consistency undecidable, even when transitive roles never occur in the cardinality constraints and these use no constants other than 0 and 1.

**Theorem (Baader, Borgwardt, De Bortoli and Koopmann).** Consistency of TBoxes in $\mathcal{SSCC}$, the extension of [ALCSCC](the-description-logic-alcscc.md) with transitivity axioms $\mathrm{trans}(r)$, is undecidable. This holds even if the numerical constraints in successor restrictions contain no transitive roles and no constants other than $0$ and $1$.

Without transitivity axioms, consistency of ALCSCC TBoxes is EXPTIME-complete. The interaction of transitive roles and number restrictions with role inclusions was known to cause undecidability (Horrocks, Sattler and Tobies); here undecidability holds under all the syntactic restrictions that regain decidability in those settings.

## Depends on

- [The description logic ALCSCC](the-description-logic-alcscc.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](../../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

The proof adapts the reduction of Horrocks, Sattler and Tobies from the tiling problem. For a tiling problem $P = (T, H, V)$ the TBox $\mathcal T_P$ gives every individual exactly one tile concept $A_t$ and exactly one $h$- and one $v$-successor ($\top \sqsubseteq \mathrm{succ}(|h| = 1 \wedge |v| = 1)$), and encodes the matching conditions by inclusions $A_t \sqsubseteq \mathrm{succ}(h \subseteq \bigsqcup_{(t, t') \in H} A_{t'})$ and likewise for $v$. A single transitive role containing $h$ and $v$ would give infinitely many successors, contradicting finite branching; instead roles $h_i, v_j$ and transitive roles $r_{ij}$ with $h_i \sqsubseteq r_{ij}$, $v_j \sqsubseteq r_{ij}$ ($i, j \in \{0, 1\}$) are used, with concept names $A_{ij}$ enforcing an alternating pattern so that an individual in $A_{ij}$ has $h = h_i$, $v = v_j$ and finitely many $r_{ij}$-successors. The $h$-successor of the $v$-successor and the $v$-successor of the $h$-successor of an individual are both its successors by transitivity, and the inclusion $\top \sqsubseteq \mathrm{succ}(|h^c \cap v^c| = 1)$ forces them to coincide, so $h \circ v$ and $v \circ h$ are equal and functional (Lemma 12). Models of $\mathcal T_P$ thus contain grids, and $P$ has a solution iff $\mathcal T_P$ is consistent (Lemma 13).

## Sources

- F. Baader, S. Borgwardt, F. De Bortoli and P. Koopmann, "Concrete Domains Meet Expressive Cardinality Restrictions in Description Logics", in *Automated Deduction – CADE 30*, Lecture Notes in Computer Science 15943, Springer, 2025, pp. 676–695, <https://doi.org/10.1007/978-3-031-99984-0_35>; numbers from the extended version arXiv:2505.21103v1, <https://arxiv.org/abs/2505.21103v1>: Section 6, Theorem 6; Appendix C.2 (the TBox $\mathcal T_P$, Definition 7, Lemmas 12 and 13).
- I. Horrocks, U. Sattler and S. Tobies, "Practical reasoning for very expressive description logics", *Logic Journal of the IGPL* 8(3):239–263, 2000, <https://doi.org/10.1093/jigpal/8.3.239>: undecidability from transitive roles in number restrictions and the reduction adapted here, as recalled in Section 6 of the version of the first source read.
