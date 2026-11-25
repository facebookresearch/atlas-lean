# Three cases of a jump from an active state with positive residuals

Let $K$ be a [valid](is-valid.md) [two-channel chain](two-channel.md) on a set $\iota$, so that its
rates $\lambda_1, \lambda_2$ are nonnegative, with [total rate](total-rate.md)
$q = \lambda_1 + \lambda_2$. Let $y$ be an active state, $q(y) \ne 0$, and $r = (r_1, r_2)$ residual
clocks with $r_1 > 0$ and $r_2 > 0$; write $\lambda_k = \lambda_k(y)$. Then one of the following
three mutually exclusive cases holds:

1. channel $1$ rings first: $\lambda_2 r_1 < \lambda_1 r_2$, and $\lambda_1 > 0$;
2. channel $2$ rings first: $\lambda_1 r_2 < \lambda_2 r_1$ (so $\lambda_2 r_1 < \lambda_1 r_2$
   fails), and $\lambda_2 > 0$;
3. a tie: neither strict inequality holds, so $\lambda_1 r_2 = \lambda_2 r_1$, and $\lambda_1 > 0$,
   $\lambda_2 > 0$ and $\lambda_2 r_1 / \lambda_1 = r_2$; both channels ring at the same time
   $r_1 / \lambda_1 = r_2 / \lambda_2$.
