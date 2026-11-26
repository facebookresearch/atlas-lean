# Maskin monotonicity and single-voter monotonicity

Let $f$ map profiles of strict rankings of alternatives $A$ by voters $V$ to alternatives. It is *Maskin monotone* if whenever $f(P) = a$ and $Q$ is a profile in which, for every voter, every alternative ranked below $a$ in $P$ remains below $a$ in $Q$, then $f(Q) = a$. It is *single-voter monotone* if whenever changing one voter $i$'s ranking from $P_i$ to $Q_i$ changes the outcome from $a$ to $a'$, then $i$ ranks $a$ above $a'$ at $P_i$ and $a'$ above $a$ at $Q_i$.

## Depends on

- [Social choice functions](../gibbard-satterthwaite-theorem/social-choice-function.md)
- [Strategy-proof social choice function](../gibbard-satterthwaite-theorem/is-strategy-proof.md)

## Sources

- Noam Nisan, "Introduction to Mechanism Design (for Computer Scientists)", Algorithmic Game Theory, Cambridge University Press, 2007.
- Eitan Muller and Mark A. Satterthwaite, "The Equivalence of Strong Positive Association and Strategy-Proofness", Journal of Economic Theory, 1977.
