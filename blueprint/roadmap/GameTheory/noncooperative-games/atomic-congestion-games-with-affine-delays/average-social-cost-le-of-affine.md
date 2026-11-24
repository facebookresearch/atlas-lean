# Price of anarchy 5/2 for no-regret play in affine congestion games

In a congestion game with affine delays $d_e(n) = a_e n + b_e$, $a_e, b_e \ge 0$, and players $I$,
if after $T \ge 1$ rounds every player's regret against every fixed strategy is at most
$T\varepsilon$, then the time-averaged social cost satisfies

$$\frac1T \sum_{k=1}^T C(s^k) \le \tfrac52\, C(t) + \tfrac32\, |I|\, \varepsilon$$

for every profile $t$.

## Informally uses

- [Affine congestion games are (5/3, 1/3)-smooth](is-smooth-of-affine.md) and
  [Robust price of anarchy for no-regret dynamics](../no-regret-dynamics/average-social-cost-le.md).

## Sources

- T. Roughgarden, "Intrinsic robustness of the price of anarchy", J. ACM 62(5) (2015), Article 32, Example 2.5 and Theorem 3.3.
