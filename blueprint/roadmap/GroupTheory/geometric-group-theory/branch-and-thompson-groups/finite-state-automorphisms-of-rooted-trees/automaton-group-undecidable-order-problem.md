# Some automaton group has undecidable order problem

There is an automaton group in which no algorithm decides whether a given element has finite order. This answers a question of Grigorchuk, Nekrashevych and Sushchanskii.

There exists an invertible Mealy automaton $\mathcal{A}$ such that the automaton group $G$ it generates has undecidable order problem: no algorithm decides, given a word over the generators $\sigma_p$ and their inverses, whether it represents an element of finite order in $G$ (Theorem 1.1 and Theorem 6.1 of the source). In the construction the elements of finite order that encode halting computations have order a power of $2$.

Automaton groups have decidable word problem, so by Higman's embedding theorem and a theorem of Clapham such a group embeds in a finitely presented group with decidable word problem and undecidable order problem, a new proof of McCool's theorem.

## Depends on

- [Automaton group](automaton-group.md)
- [Order problem and torsion problem of a finitely generated group](../../../presentations-and-decision-problems/conjugacy-order-and-power-problems/order-and-power-problems/order-problem.md)
- [Group](../../../group-basics/group.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The halting problem for single-tape machines is undecidable](../../../../TheoryOfComputation/computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

For a Turing machine $M$, simulated by a one-dimensional cellular automaton, the source builds a Mealy automaton generating a group $G(M)$ and, for each input word $w$, a computable element $g \in G(M)$ that acts on encodings of the successive configurations $w_0 \# w_1 \# \cdots$, with $\#$ a separator symbol, with synchronized counters. One step of the cellular automaton corresponds to squaring the element, and $g$ has finite order (then a power of $2$) exactly when $M$ halts on $w$. Taking $M$ universal gives an automaton group with undecidable order problem.

## Sources

- P. Gillibert, "An automaton group with undecidable order and Engel problems", Journal of Algebra 497 (2018), 363–392, https://doi.org/10.1016/j.jalgebra.2017.11.049; arXiv:1710.09733v2 (Theorem 1.1 and Theorem 6.1 of arXiv:1710.09733v2).
