# Entry fees and pay-your-dues deter whitewashing

Consider the randomly matched repeated prisoner's dilemma with stage payoffs $\pi(C,C) = 1$, $\pi(D,D) = 0$, $\pi(D,C) = 2$, $\pi(C,D) = -1$, discount factor $0 \le \delta < 1$ and discounted average payoff $(1 - \delta)\sum_t \delta^t \pi_t$, in which reputations are public and any player may *whitewash*: leave and re-register under a fresh pseudonym with a good reputation.

- **Entry fee.** If every registration costs $f$, then deviating once and re-registering is unprofitable against reputational grim if and only if $\delta f \ge 1$, that is $f \ge 1/\delta$; reputational grim is then a subgame-perfect equilibrium when also $\delta \ge 1/2$, the condition that deters deviation without whitewashing.
- **Pay your dues.** Without fees, the pay-your-dues strategy (play $C$ against a veteran who has never deviated from it and $D$ against any other veteran; play $D$ against a newcomer unless oneself a newcomer, in which case play $C$) yields a subgame-perfect equilibrium. An encounter between a veteran and a newcomer yields total payoff $2 - 1 = 1$ instead of the $2$ of mutual cooperation, so the possibility of whitewashing imposes a social cost.

## Proof sketch

Deviating once and re-registering gives $(1 - \delta)(2 - f + \delta(1 - f) + \delta^2 + \cdots)$ against $(1 - \delta)(1 - f + \delta + \delta^2 + \cdots)$ for following reputational grim; the difference is $(1 - \delta)(1 - \delta f)$. Under pay your dues a whitewasher is treated as a newcomer, so whitewashing costs at least the punishment it escapes.

## Depends on

- [Subgame-perfect trigger strategies in the repeated prisoner’s dilemma](subgame-perfect-trigger-strategies-in-the-repeated-prisoners-dilemma.md)

## Sources

- Eric Friedman, Paul Resnick and Rahul Sami, "Manipulation-Resistant Reputation Systems", Algorithmic Game Theory, Cambridge University Press, 2007, Sections 27.2 and 27.3.
- Eric J. Friedman and Paul Resnick, "The Social Cost of Cheap Pseudonyms", Journal of Economics & Management Strategy, 2001.
