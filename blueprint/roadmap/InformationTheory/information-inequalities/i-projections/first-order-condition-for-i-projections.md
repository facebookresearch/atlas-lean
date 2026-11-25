# First-order condition for an I-projection

Under the hypotheses of the [Pythagorean inequality](pythagorean-inequality-for-i-projections.md),
every $P \in \Gamma$ vanishes wherever $P^*$ does, and

$$\sum_a (P(a) - P^*(a))\,(\log P^*(a) - \log Q(a)) \ge 0.$$

The sum is the one-sided derivative at $t = 0$ of $t \mapsto D(P^* + t(P - P^*) \| Q)$, the quantity
(3.1) of the tutorial. The proof bounds the difference quotient on $(0,1)$ from above by the
[segment estimate](first-order-estimate-along-a-segment.md), writes it as a function continuous at
$0$ plus $c \log t$ with $c = \sum_{a : P^*(a) = 0} P(a)$, and lets $t \to 0^+$: if $c > 0$ the
quotient tends to $-\infty$, contradicting minimality, which proves the support claim.

## Sources

- I. Csiszár and P. C. Shields, *Information Theory and Statistics: A Tutorial*, Foundations and Trends in Communications and Information Theory 1(4) (2004), 417–528, proof of Theorem 3.1, (3.1).
