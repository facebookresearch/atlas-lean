# Model checking hyperlogics with pushdown automata is undecidable

For hyperlogics that quantify over traces of a finite transition system and check the quantified traces with an ω-pushdown automaton, model checking is undecidable as soon as one universal quantifier is allowed; with visibly pushdown automata it is undecidable exactly when the stack may depend on a non-initial quantifier block.

**Logics.** A *transition system* $\mathcal T=(V,E,V_I,\lambda)$ has finitely many vertices labeled by letters of $\Sigma$, and its traces are the label sequences of its infinite paths from initial vertices. An *ω-pushdown automaton* (ω-PDA) is a pushdown automaton on infinite words with Büchi acceptance; it is *visibly* (an ω-VPA) if its input alphabet is partitioned into call, return and skip letters that push one symbol, pop one symbol, and leave the stack unchanged, respectively. A formula of HyperPDA has the form $Q_0\pi_0.\,Q_1\pi_1.\cdots Q_{k-1}\pi_{k-1}.\,\mathcal A$ with quantifiers $Q_i\in\{\exists,\forall\}$ over traces and an ω-PDA $\mathcal A$ over $\Sigma^k$, which must accept the $k$-tuple of quantified traces read letter by letter. HyperVPA is the restriction to ω-VPA. $\Sigma_n$ and $\Pi_n$ are the formulas with $n-1$ quantifier alternations beginning with $\exists$, respectively $\forall$. An ω-VPA over $\Sigma^k$ is *controlled* by a set $I$ of indexes if whether a letter is a call, return or skip depends only on its components in $I$, and $\Sigma_{n,j}$, $\Pi_{n,j}$ are the HyperVPA formulas in $\Sigma_n$, $\Pi_n$ whose automaton is controlled by the indexes of the $j$-th quantifier block. *Model checking* asks whether the traces of a given transition system satisfy a given formula.

**Theorem (Winter and Zimmermann).**

1. HyperPDA model checking is undecidable for $\Pi_1$ formulas, hence for all $\Sigma_n$ with $n>1$ and all $\Pi_n$ with $n\ge1$ (Theorem 2(2) and Corollary 3; it follows at once from undecidable universality of ω-pushdown automata).
2. HyperVPA model checking is undecidable for $\Pi_{2,2}$ formulas (Theorem 19), and hence for $\Sigma_{n,j}$ and $\Pi_{n,j}$ whenever $n>1$ and $1<j\le n$ (Corollary 20). The extended version strengthens the first claim to ω-VPA with weak parity acceptance with three colors.

On the decidable side, HyperPDA model checking for $\Sigma_1$ formulas is in EXPTIME and PSPACE-hard, HyperVPA model checking for $\Pi_1$ formulas is EXPTIME-complete, and for formulas with one quantifier alternation whose stack depends only on the initial quantifier block it is decidable; the extended version (with Kuske) shows decidability of $\Sigma_{n,1}$ and $\Pi_{n,1}$ in $n$-fold exponential time for every $n$. Both logics subsume [HyperLTL](hyperltl.md).

## Depends on

- [Kripke structures with initial states](kripke-structures-with-initial-states.md)
- [HyperLTL](hyperltl.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The complement of PCP many-one reduces to universality of context-free grammars](../../../TheoryOfComputation/undecidable-problems/universality-problem-for-context-free-grammars/many-one-reducible-not-pcp-univ.md)

## Expansion

Part 1 is immediate from the undecidability of universality of ω-pushdown automata: a $\Pi_1$ formula $\forall\pi.\,\mathcal A$ over a transition system generating all words states that $\mathcal A$ is universal. For part 2, the universal quantifier ranges over input words $w$ and the existential one over sequences of transitions of a pushdown automaton for a context-free grammar; an ω-VPA controlled by the second component simulates the transition sequence, using the transitions themselves to decide whether to push or pop, and checks that it is an accepting run on $w$, so the $\Pi_{2,2}$ formula holds exactly when the grammar's language is universal. A good expansion links a page for undecidability of universality of ω-pushdown automata, which has no page yet.

## Sources

- S. Winter and M. Zimmermann, "Logics for context-free hyperproperties", in *51st International Symposium on Mathematical Foundations of Computer Science (MFCS 2026)*, Leibniz International Proceedings in Informatics 386, pp. 54:1–54:18, 2026, doi:[10.4230/LIPIcs.MFCS.2026.54](https://doi.org/10.4230/LIPIcs.MFCS.2026.54), read in the open-access publisher copy, whose numbering is used for the theorem: Theorem 2, Corollaries 3 and 6, Theorems 7, 16 and 19 and Corollary 20; also read in the extended version by D. Kuske, S. Winter and M. Zimmermann, arXiv:2605.04657v3 ([arXiv](https://arxiv.org/abs/2605.04657v3)): the definitions of transition systems, ω-PDA and ω-VPA in the preliminaries, HyperPDA and HyperVPA and their fragments in the section "Logics for Context-Free Hyperproperties", Theorem 3 (decidability of $\Sigma_{n,1}$ and $\Pi_{n,1}$), and Theorem 4 with the weak parity remark after its proof.
