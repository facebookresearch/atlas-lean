# Finite games with a computable winning function

In such a game two players alternately choose natural numbers for a fixed number m of moves, with perfect information, and a computable function of the m choices names the winner. By a theorem of Kalmár, exactly one player has a winning strategy.

Fix $m \ge 1$ and a computable function $W \colon \mathbb{N}^m \to \{\mathrm{A}, \mathrm{B}\}$. In the game $\mathcal{G}(m, W)$:

- the players A and B alternately choose natural numbers, A first, and the game ends after $m$ numbers $x_1, \dots, x_m$ have been chosen (A chooses $x_1, x_3, \dots$, B chooses $x_2, x_4, \dots$);
- there is perfect information: each player knows $m$, $W$ and all earlier choices;
- the winner is $W(x_1, \dots, x_m)$.

As a Gale–Stewart game, $\mathcal{G}(m, W)$ is the game on $\mathbb{N}$ with payoff set
$S_W = \{ s \in \mathbb{N}^{\mathbb{N}} : W(s(0), \dots, s(m-1)) = \mathrm{A} \}$, A playing as player I and B as player II. The payoff depends only on the first $m$ moves, so a winning strategy for A (resp. B) in the finite game extends, by playing $0$ after the first $m$ moves, to a winning strategy for player I (resp. II), and such a strategy restricts back to the first $m$ moves. Accordingly, *A has a winning strategy in $\mathcal{G}(m, W)$* means that [player I wins](../../../SetTheory/determinacy/gale-stewart-games/iwins.md) the game with payoff $S_W$, and *B has a winning strategy* means that [player II wins](../../../SetTheory/determinacy/gale-stewart-games/iiwins.md) it. As an instance of the decision problem, a game is given by $m$ and a program computing $W$.

By a theorem of Kalmár, building on Zermelo and Kőnig, exactly one of the two players has a winning strategy in every such game; here every move has infinitely many options, unlike Zermelo's finite case. In the formulation above, $S_W$ is a union of cylinders of length $m$, hence open, so at least one player wins by the [Gale–Stewart theorem for open payoff sets](../../../SetTheory/determinacy/gale-stewart-games/determined-of-is-open.md), and [at most one player wins](../../../SetTheory/determinacy/gale-stewart-games/not-i-wins-and-ii-wins.md).

## Depends on

- [Player I wins a game](../../../SetTheory/determinacy/gale-stewart-games/iwins.md)
- [Player II wins a game](../../../SetTheory/determinacy/gale-stewart-games/iiwins.md)

## Proof depends on

None.

## Expansion

Many games of no chance with perfect information and a bounded number of moves fit this framework after the moves are coded by natural numbers.

## Sources

- B. Poonen, "Undecidable problems: a sampler", in J. Kennedy (ed.), *Interpreting Gödel: Critical Essays*, Cambridge University Press, 2014, pp. 211–241; read as arXiv:1204.0299v2, <https://arxiv.org/abs/1204.0299v2>: Section 14.1, "Abstract games".
- L. Kalmár, "Zur Theorie der abstrakten Spiele", *Acta Scientiarum Mathematicarum (Szeged)* 4:65–85, 1928–29, cited by the survey for determinacy (not read here).
