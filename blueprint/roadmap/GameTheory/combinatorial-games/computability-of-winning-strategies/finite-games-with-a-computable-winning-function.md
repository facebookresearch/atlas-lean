# Finite games with a computable winning function

In such a game two players alternately choose natural numbers for a fixed number m of moves, with perfect information, and a computable function of the m choices names the winner. Exactly one player has a winning strategy, but which one need not be computable.

Fix $m \ge 1$ and a computable function $W \colon \mathbb{N}^m \to \{\mathrm{A}, \mathrm{B}\}$. In the game $\mathcal{G}(m, W)$:

- the players A and B alternately choose natural numbers, A first, and the game ends after $m$ numbers $x_1, \dots, x_m$ have been chosen (A chooses $x_1, x_3, \dots$, B chooses $x_2, x_4, \dots$);
- there is perfect information: each player knows $m$, $W$ and all earlier choices;
- the winner is $W(x_1, \dots, x_m)$.

A *strategy* for a player assigns to every sequence of earlier choices at which that player moves the number to choose; it is *winning* if every play following it is won by that player, and *computable* if it is given by a computable function of the earlier choices. As an instance of the decision problem, a game is given by $m$ and a program computing $W$.

By a theorem of Kalmár, building on Zermelo and Kőnig, exactly one of the two players has a winning strategy in every such game; the finite-tree case is Zermelo's determinacy theorem for finite two-person win-lose games, while here every move has infinitely many options.

## Depends on

None.

## Proof depends on

None.

## Expansion

Many games of no chance with perfect information and a bounded number of moves fit this framework after the moves are coded by natural numbers.

## Sources

- B. Poonen, "Undecidable problems: a sampler", in J. Kennedy (ed.), *Interpreting Gödel: Critical Essays*, Cambridge University Press, 2014, pp. 211–241; read as arXiv:1204.0299v2, <https://arxiv.org/abs/1204.0299v2>: Section 14.1, "Abstract games".
- L. Kalmár, "Zur Theorie der abstrakten Spiele", *Acta Scientiarum Mathematicarum (Szeged)* 4:65–85, 1928–29, cited by the survey for determinacy (not read here).
