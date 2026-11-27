# Monadic second-order logic with the ultimately periodic quantifier

MSO+P extends monadic second-order logic over $\omega$-words by a quantifier $\mathsf{P} X.\,\varphi(X)$ that says $\varphi(X)$ is true for every ultimately periodic set $X$ of positions.

**Definition.** A set $X \subseteq \mathbb{N}$ is *ultimately periodic* if there are a period $p \geq 1$ and a threshold $n_0$ such that for all $x \geq n_0$, $x \in X$ iff $x + p \in X$. *MSO+P* over $\omega$-words (structures $(\mathbb{N}, <, (P_a)_{a \in \Sigma})$ for a finite alphabet $\Sigma$) is [monadic second-order logic](../../../../TheoryOfComputation/omega-automata-and-games/logic-and-tree-automata/monadic-second-order-logic-over-words.md), with first-order and set quantifiers ranging over positions and arbitrary sets of positions, extended by formulas $\mathsf{P} X.\,\varphi(X)$, where $\varphi$ may have further free variables, with the semantics: $\mathsf{P} X.\,\varphi(X)$ is true iff $\varphi(X)$ is true for every ultimately periodic $X \subseteq \mathbb{N}$. The *satisfiability problem over $\omega$-words* asks whether a given sentence is true in some $\omega$-word.

**Related predicate.** A set $X \subseteq \mathbb{N}$ satisfies the predicate $\mathsf{W}(X)$ if for every $k \in \mathbb{N}$ there are two consecutive elements of $X$ at distance at least $k$. *MSO+W* adds this predicate to MSO.

## Depends on

- [Monadic second-order logic over words](../../../../TheoryOfComputation/omega-automata-and-games/logic-and-tree-automata/monadic-second-order-logic-over-words.md)

## Proof depends on

None.

## Expansion

Every ultimately periodic set is determined by finitely many data, so the quantifier $\mathsf{P}$ ranges over a countable family; the question whether MSO+P has decidable satisfiability was raised by Bojańczyk and Colcombet. MSO+W is a fragment of [MSO+U](monadic-second-order-logic-with-the-unbounding.md): $\mathsf{W}(X)$ says that there are intervals disjoint from $X$ of arbitrarily large size.

## Sources

- M. Bojańczyk, L. Daviaud, B. Guillon, V. Penelle and A. V. Sreejith, "Undecidability of a weak version of MSO+U", *Logical Methods in Computer Science* 16(1), 2020, paper 12, doi:10.23638/LMCS-16(1:12)2020; read as arXiv:1807.08506v5, <https://arxiv.org/abs/1807.08506v5>: Section 1 (the predicate $\mathsf{W}$, the logic MSO+W, ultimately periodic sets and the quantifier $\mathsf{P}$).
