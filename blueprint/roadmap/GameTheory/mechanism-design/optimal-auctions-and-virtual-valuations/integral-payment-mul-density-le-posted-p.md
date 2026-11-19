# The optimal mechanism for one bidder

Let $a < b$ and let the bidder's value have a density $f : \mathbb{R} \to \mathbb{R}$ that is continuous and positive on $[a, b]$ with $\int_a^b f = 1$; write $F(t) = \int_a^t f$ and $\varphi$ for the virtual valuation. A single-parameter mechanism has an allocation rule $Q$ and a payment rule $P$ (real functions on $\mathbb{R}$), and $U(t) = t\,Q(t) - P(t)$ is the truthful utility.
Let $r \in [a, b]$ separate the values of negative and nonnegative virtual valuation: $\varphi(t) \le 0$ for
$t \in [a, b]$ with $t < r$, and $\varphi(t) \ge 0$ for $t \in [a, b]$ with $t > r$ (as when $\varphi$ is
increasing and $r = \varphi^{-1}(0)$, or $r = a$ when $\varphi \ge 0$ throughout, or $r = b$ when
$\varphi \le 0$ throughout). Then the posted price $r$ earns at least as much as every mechanism $(Q, P)$
that is incentive compatible on $[a, b]$, has $0 \le Q \le 1$ on $[a, b]$ and gives the lowest type
$U(a) \ge 0$:

$$\int_a^b P(t)\,f(t)\,dt \le \int_a^b P_r(t)\,f(t)\,dt$$

(Myerson 1981, §5, for one bidder and seller value $t_0 = 0$: the optimal auction sells exactly to the types
with nonnegative virtual valuation, at the lowest winning bid $r$).

## Informally uses

- [Revenue bound from a single bidder](integral-payment-mul-density-le.md): the upper bound.
- [Revenue of a posted price](integral-posted-price-payment-mul-densit.md): the posted price $r$ attains it.

## Sources

- R. B. Myerson, "Optimal auction design", *Mathematics of Operations Research* 6(1) (1981), 58–73, §5, (5.6) and (5.7), and the example with values uniform on `[0, 100]`, where the optimal reserve price is `50` and the expected revenue `25`.
