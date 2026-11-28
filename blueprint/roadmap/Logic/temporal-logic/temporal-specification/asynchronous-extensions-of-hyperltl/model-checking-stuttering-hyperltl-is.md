# Model checking stuttering HyperLTL is undecidable

Model checking finite Kripke structures against HyperLTL with stutter-relativized temporal modalities is undecidable, already for alternation-free sentences whose modalities are relativized to the empty set and to a set of atomic propositions.

**Theorem (Bozzelli, Peron and Sánchez).** For a finite set $\Gamma$ of LTL formulas and a trace $\pi$, the *$\Gamma$-stutter factorization* of $\pi$ splits it into maximal nonempty segments on which every formula of $\Gamma$ keeps its truth value; the *$\Gamma$-successor* of a position $i$ is the first position of the next segment, or $i + 1$ if $i$ lies in the last, infinite segment. *Stuttering HyperLTL* (HyperLTL$_S$) has the sentences $Q_1 x_1 \cdots Q_n x_n\,\psi$ of HyperLTL, with trace quantifiers $Q_i \in \{\exists, \forall\}$ over the traces of a Kripke structure, whose quantifier-free part $\psi$ is built from atoms $p[x]$, Boolean connectives and modalities $\mathsf X_\Gamma$ and $\mathsf U_\Gamma$ for finite sets $\Gamma$ of LTL formulas: $\mathsf X_\Gamma\psi$ moves every quantified trace to its $\Gamma$-successor, and $\mathsf U_\Gamma$ iterates this move, so that the quantified traces are traversed in lockstep along their $\Gamma$-stutter factorizations. The model-checking problem for HyperLTL$_S$ is undecidable, even for sentences of quantifier alternation depth $0$ whose temporal modalities use only two sets $\Gamma$, one empty and the other consisting of atomic propositions (Theorem III.1 of the source).

With $\Gamma = \emptyset$ the modalities are those of HyperLTL, whose model checking is decidable. The source identifies a fragment, simple HyperLTL$_S$, with decidable model checking (Section III-D of the source).

## Depends on

- [Kripke structures with initial states](../kripke-structures-with-initial-states.md)
- [HyperLTL](../hyperltl.md)
- [Formulas of linear temporal logic](../../linear-temporal-logic/formula.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The Post correspondence problem is undecidable](../../../../TheoryOfComputation/undecidable-problems/post-correspondence-problem/exists-not-tm2-decidable-pcp.md)

## Expansion

The proof reduces the Post correspondence problem, assuming, without loss of generality as the source notes, that all words of the instance have length at least $2$. For a sequence of indices $i_1, \ldots, i_k$ and $\ell \in \{1, 2\}$, a well-formed trace writes $u^\ell_{i_1} \cdots u^\ell_{i_k}$, marking each letter of $u^\ell_i$ with propositions $p_i$ and $q_\ell$ and the last letter of each block with $\#$. For $\Gamma = \{\#, p_1, \ldots, p_n\}$ the $\Gamma$-stutter trace of such a trace records just the index sequence. The instance has a solution iff there are well-formed traces $\pi_1$ (marked $q_1$) and $\pi_2$ (marked $q_2$) with the same letters position by position and with $\Gamma$-stutter traces that agree on $\Gamma$ (Proposition III.3); an existential sentence with modalities relativized to $\emptyset$ and to $\Gamma$ expresses this over a suitable Kripke structure (Proposition III.4).

## Sources

- L. Bozzelli, A. Peron and C. Sánchez, "Asynchronous Extensions of HyperLTL", in *2021 36th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS)*, IEEE, 2021, pp. 1–13, <https://doi.org/10.1109/LICS52264.2021.9470583>; numbers from arXiv:2104.12886v1, <https://arxiv.org/abs/2104.12886v1>: Definitions III.1 and III.2, Section III-B (syntax and semantics, Remark III.1), Section III-C (Theorem III.1 and Propositions III.3, III.4) and Section III-D.
