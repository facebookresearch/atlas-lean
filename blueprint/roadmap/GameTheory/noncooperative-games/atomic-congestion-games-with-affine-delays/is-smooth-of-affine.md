# Affine congestion games are (5/3, 1/3)-smooth

Let a congestion game have affine delays $d_e(n) = a_e n + b_e$ with $a_e, b_e \ge 0$. Then for all
profiles $s$ and $t$,

$$\sum_i c_i(t_i, s_{-i}) \le \tfrac53\, C(t) + \tfrac13\, C(s),$$

where $C$ is the social cost: the game is $(5/3, 1/3)$-smooth.

With loads $x_e = n_e(s)$ and $y_e = n_e(t)$, the left side is at most
$\sum_e y_e\,(a_e(x_e + 1) + b_e)$, and the Christodoulou–Koutsoupias inequality bounds each term
by $\tfrac53 (a_e y_e + b_e) y_e + \tfrac13 (a_e x_e + b_e) x_e$.

## Informally uses

- [Christodoulou–Koutsoupias inequality](nat-mul-succ-le.md),
  [Load after a unilateral deviation](load-update-le.md) and
  [Counting resource usage](sum-sum-uses.md).

## Background

- [Smooth game](../no-regret-dynamics/is-smooth.md): the definition being verified.

## Sources

- T. Roughgarden, "Intrinsic robustness of the price of anarchy", J. ACM 62(5) (2015), Article 32, Example 2.5.
