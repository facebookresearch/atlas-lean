# Positive two-variable intuitionistic logic with one monadic letter is undecidable

There is no algorithm that decides which positive first-order formulas with two individual variables and a single monadic predicate letter, without constants, function symbols or equality, are theorems of intuitionistic predicate logic.

**Theorem (Rybakov and Shkatov).** The positive fragment of [$\mathbf{QInt}$](quantified-intuitionistic-logic-qint.md) in the language with two individual variables and a single predicate letter, which is monadic, is undecidable: no algorithm decides, for $\bot$-free formulas built from one unary letter $P$, the variables $x, y$, the constant $\top$, the connectives $\wedge$, $\vee$, $\to$ and the quantifiers $\exists$, $\forall$, whether they belong to $\mathbf{QInt}$.

Remark 3.10 of the source states that the results of its Section 3 also hold for Kripke frames with constant domains. Since all logics between $\mathbf{QInt}$ and $\mathbf{QKC}$ share their positive fragment, the same holds for each of them, and a modification of the construction gives the same conclusion for every logic between the first-order counterparts $\mathbf{QBL}$ and $\mathbf{QFL}$ of Visser's basic and formal logics (Theorems 3.8 and 3.9 of the source).

## Depends on

- [Quantified intuitionistic logic $\mathbf{QInt}$](quantified-intuitionistic-logic-qint.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [The tiling problem is undecidable](../../../TheoryOfComputation/undecidable-problems/wang-tiles/the-tiling-problem-is-undecidable.md)

## Expansion

Kontchakov, Kurucz and Zakharyaschev (2005) showed that the two-variable fragment of $\mathbf{QInt}$ is undecidable by reducing the complement of the $\mathbb{N} \times \mathbb{N}$ tiling problem. The source first makes that encoding positive and monadic: binary letters are simulated by monadic ones in the positive fragment, giving undecidability of the positive monadic two-variable fragment (Theorem 3.4). It then embeds that fragment into the subfragment with one monadic letter, adapting a propositional technique of Rybakov that reduces positive intuitionistic formulas to formulas in two variables: each letter $P_i$ is replaced by a positive formula in the single letter $P$ that, in a countermodel built over a fixed layered frame, defines the worlds where $P_i$ holds. The translation $\varphi \mapsto \varphi^\ast$ satisfies $\varphi \in \mathbf{QInt}$ iff $\varphi^\ast \in \mathbf{QInt}$ and introduces no new individual variables.

## Sources

- M. Rybakov and D. Shkatov, "Undecidability of first-order modal and intuitionistic logics with two variables and one monadic predicate letter", *Studia Logica* 107(4):695–717, 2019, doi:10.1007/s11225-018-9815-7; read as arXiv:1706.05060v5, <https://arxiv.org/abs/1706.05060v5>: Theorem 3.7 of arXiv:1706.05060v5 (with Theorem 3.4 and Remark 3.10).
