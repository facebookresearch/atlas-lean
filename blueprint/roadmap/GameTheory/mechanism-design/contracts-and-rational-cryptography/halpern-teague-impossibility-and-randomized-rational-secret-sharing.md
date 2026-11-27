# Halpern–Teague impossibility and randomized rational secret sharing

In the rational secret sharing game, withholding one's share weakly dominates broadcasting in the one-shot simultaneous game, and in every protocol with a commonly known bounded number of rounds, iterated deletion of weakly dominated strategies (backward induction) eliminates broadcasting, leaving every party with payoff $U^-$. By contrast, a protocol in which each round is the real reconstruction round with a geometric probability $\beta$, unknown to the parties until after the round, makes honest broadcasting a strict Nash equilibrium at every stage, and it is $k$-resilient against coalitions when $\beta$ is small enough relative to the utility gaps.

## Proof sketch

If the others' behaviour does not depend on one's own share, withholding never hurts and strictly helps when exactly $t - 1$ others broadcast. With a known last round this argument unravels backwards. With a hidden random real round, withholding in a round risks forfeiting the secret with probability $1 - \beta$, which outweighs the gain $U^+ - U$ for small $\beta$.

## Depends on

- [Rational secret sharing game](rational-secret-sharing-game.md)
- [Iterated deletion of strictly dominated strategies](../../noncooperative-games/nash-s-theorem/dominance-and-iterated-deletion/iterated-deletion-of-strictly-dominated-strategies.md)
- [Strong equilibrium, strong Nash equilibrium and k-resilience](../../noncooperative-games/potential-games/strong-and-coalitional-equilibria/strong-equilibrium-strong-nash-equilibrium-and-k-resilience.md)

## Sources

- Joseph Y. Halpern and Vanessa Teague, "Rational Secret Sharing and Multiparty Computation: Extended Abstract", Proceedings of the Thirty-Sixth Annual ACM Symposium on Theory of Computing (STOC 2004), 2004.
- Ittai Abraham, Danny Dolev, Rica Gonen and Joseph Y. Halpern, "Distributed Computing Meets Game Theory: Robust Mechanisms for Rational Secret Sharing and Multiparty Computation", Proceedings of the Twenty-Fifth Annual ACM Symposium on Principles of Distributed Computing (PODC 2006), 2006.
- Yevgeniy Dodis and Tal Rabin, "Cryptography and Game Theory", Algorithmic Game Theory, Cambridge University Press, 2007.
