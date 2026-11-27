# Halpern–Teague impossibility and randomized rational secret sharing

In the rational secret sharing game with threshold $t \ge 2$, withholding one's share weakly dominates broadcasting in the one-shot simultaneous game, and in every protocol whose number of simultaneous broadcast rounds is fixed in advance (with no other physical assumptions), iterated deletion of weakly dominated strategies (backward induction) eliminates broadcasting, leaving every party with payoff $U^-$. Randomized protocols in which each round is the real reconstruction round with probability $\beta$, unknown to the parties until after the round, escape this. Suppose $k < t$, each party's utility depends only on which parties learn the secret, and each party strictly prefers learning it to not learning it. With a mediator that runs such a protocol, honest play is a $k$-resilient equilibrium that survives iterated deletion of weakly dominated strategies (no coalition of at most $k$ parties has a joint deviation that makes any of its members better off) whenever $\beta$ is at most an explicit bound determined by the utility gaps, and the expected number of rounds is $O(1/\beta)$. Without a mediator, assuming cryptography (enhanced trapdoor permutations), for every $\varepsilon > 0$ there is such a protocol in which no member of a coalition of at most $k$ parties gains more than $\varepsilon$ by deviating.

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
