# Nash equilibria of two-player extensive games via sequence-form complementarity

In a two-player extensive-form game with perfect recall, a pair of realization plans $(x, y)$ corresponds to a Nash equilibrium (in behavior or mixed strategies) if and only if there are dual vectors $p, q$ with $E^\top p \ge A_1 y$, $F^\top q \ge A_2^\top x$, and the complementarity conditions $x^\top (E^\top p - A_1 y) = 0$ and $y^\top (F^\top q - A_2^\top x) = 0$. Consequently every such game has a Nash equilibrium in behavior strategies.

## Proof sketch

Complementary slackness of the best-response linear programs is exactly the condition that each plan is a best response. Existence follows from Nash's theorem on the strategic form together with Kuhn's theorem.

## Depends on

- [Sequence-form payoff matrices](sequence-form-payoff-matrices.md)
- [Sequence form and realization plans](sequence-form-and-realization-plans.md)

## Proof depends on

- [Sequence-form best responses are linear programs](sequence-form-best-responses-are-linear-programs.md)
- [Kuhn's theorem on behavior strategies](kuhns-theorem-on-behavior-strategies.md)
- [Nash's theorem](../../nash-s-theorem/exists-is-mixed-nash.md)

## Sources

- Bernhard von Stengel, "Efficient Computation of Behavior Strategies", Games and Economic Behavior, 1996.
- Bernhard von Stengel, "Equilibrium Computation for Two-Player Games in Strategic and Extensive Form", Algorithmic Game Theory, Cambridge University Press, 2007.
