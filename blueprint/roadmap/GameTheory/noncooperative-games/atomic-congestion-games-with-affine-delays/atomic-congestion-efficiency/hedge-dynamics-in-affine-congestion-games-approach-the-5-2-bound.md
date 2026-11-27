# Hedge dynamics in affine congestion games approach the 5/2 bound

In an atomic congestion game with nonnegative affine latencies whose player costs are bounded by $M$, if every player $i$ runs Hedge for $T$ rounds with learning rate $\eta_i = \sqrt{\ln |S_i| / T}/M$, then the expected social cost under the time-averaged outcome distribution is at most

$$
\tfrac52\, C(s^*) + 3 M \sum_i \sqrt{\ln |S_i| / T}
$$

for every profile $s^*$.

## Proof sketch

Combine the $(5/3, 1/3)$-smoothness of affine congestion games (Roughgarden 2015, Example 2.5) with the repeated extension theorem (Roughgarden 2015, Theorem 3.3, inequality (25)): the average cost is at most $\lambda/(1 - \mu) = 5/2$ times $C(s^*)$ plus the players' average regrets divided by $1 - \mu = 2/3$. Rescaling costs to $[0, 1]$, Hedge has average regret at most $2\sqrt{\ln |S_i| / T}$ (Lecture 17, Theorem 2.1 and its proof), that is, $2M\sqrt{\ln |S_i| / T}$ in the original costs, and $\tfrac32 \cdot 2M = 3M$.

## Depends on

- [Hedge (multiplicative-weights) dynamics in a finite game](../../no-regret-dynamics/learning-dynamics-in-games/hedge-multiplicative-weights-dynamics-in-a-finite-game.md)
- [Congestion game](../../potential-games/congestion-game.md)

## Proof depends on

- [Affine congestion games are (5/3, 1/3)-smooth](../is-smooth-of-affine.md)
- [Each player in Hedge dynamics has vanishing regret](../../no-regret-dynamics/learning-dynamics-in-games/each-player-in-hedge-dynamics-has-vanishing-regret.md)
- [Robust price of anarchy for no-regret dynamics](../../no-regret-dynamics/average-social-cost-le.md)

## Sources

- Tim Roughgarden, "CS364A: Algorithmic Game Theory, Lecture Notes", Stanford University, Fall 2013, 2013, Lecture 17, Theorem 2.1.
- Tim Roughgarden, "Intrinsic Robustness of the Price of Anarchy", Journal of the ACM, 2015, Example 2.5 and Theorem 3.3.
