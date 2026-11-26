# Hedge dynamics in affine congestion games approach the 5/2 bound

In an atomic congestion game with nonnegative affine latencies whose player costs are bounded by $M$, if every player runs Hedge for $T$ rounds, then the expected social cost under the time-averaged outcome distribution is at most

$$
\tfrac52\, C(s^*) + 3 M \sum_i \sqrt{\ln |S_i| / T}
$$

for every profile $s^*$.

## Proof sketch

Combine the $(5/3, 1/3)$-smoothness of affine congestion games with the no-regret price-of-anarchy bound; the regret term divided by $1 - \mu = 2/3$ and the Hedge regret bound give the stated additive error.

## Depends on

- [Hedge (multiplicative-weights) dynamics in a finite game](../learning-dynamics-in-games/hedge-multiplicative-weights-dynamics-in-a-finite-game.md)
- [Congestion game](../potential-games/congestion-game.md)

## Proof depends on

- [Affine congestion games are (5/3, 1/3)-smooth](../atomic-congestion-games-with-affine-delays/is-smooth-of-affine.md)
- [Each player in Hedge dynamics has vanishing regret](../learning-dynamics-in-games/each-player-in-hedge-dynamics-has-vanishing-regret.md)
- [Robust price of anarchy for no-regret dynamics](../no-regret-dynamics/average-social-cost-le.md)

## Sources

- Tim Roughgarden, "CS364A: Algorithmic Game Theory, Lecture Notes", Stanford University, Fall 2013, 2013.
- Tim Roughgarden, "Intrinsic Robustness of the Price of Anarchy", Journal of the ACM, 2015.
