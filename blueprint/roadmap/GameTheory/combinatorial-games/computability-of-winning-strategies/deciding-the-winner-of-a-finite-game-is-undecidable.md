# Deciding the winner of a finite game with a computable winning function is undecidable

No algorithm decides, given the number of moves and a program for the winning function, which player has a winning strategy in a finite game of perfect information whose moves are natural numbers.

**Theorem.** The following problem is undecidable. Input: $m \ge 1$ and a program computing a function $W \colon \mathbb{N}^m \to \{\mathrm{A}, \mathrm{B}\}$. Question: does player A have a winning strategy in the [game](finite-games-with-a-computable-winning-function.md) $\mathcal{G}(m, W)$? The proof in the source uses only one-move games ($m = 1$).

Exactly one of the players has a winning strategy (Kalmár), so the question "which player has a winning strategy?" is the same problem.

## Depends on

- [Finite games with a computable winning function](finite-games-with-a-computable-winning-function.md)
- [Decidability by multi-stack machines](../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting is undecidable](../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

Given a program $p$, consider the one-move game in which A chooses a positive integer $x_1$ and wins exactly when $p$ halts within the first $x_1$ steps. This $W$ is computable from $p$, by running $p$ for $x_1$ steps, and A has a winning strategy exactly when $p$ halts. A decision procedure for the winner would therefore decide the halting problem.

## Sources

- B. Poonen, "Undecidable problems: a sampler", in J. Kennedy (ed.), *Interpreting Gödel: Critical Essays*, Cambridge University Press, 2014, pp. 211–241; read as arXiv:1204.0299v2, <https://arxiv.org/abs/1204.0299v2>: Theorem 14.1 and its proof in Section 14.1. The survey states the result without attribution beyond the determinacy theorem of Kalmár.
