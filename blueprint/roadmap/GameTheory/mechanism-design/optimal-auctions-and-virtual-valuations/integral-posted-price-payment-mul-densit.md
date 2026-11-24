# Revenue of a posted price

Let $a, b \in \mathbb{R}$, let $f : \mathbb{R} \to \mathbb{R}$ be continuous on $[a, b]$ with
$\int_a^b f = 1$, and let $r \in [a, b]$. With the [posted-price payment](posted-price-payment.md) $P_r$,

$$\int_a^b P_r(t)\,f(t)\,dt = r\,\Bigl(1 - \int_a^r f\Bigr) = r\,(1 - F(r)).$$

When moreover $f \ge 0$ on $[a, b]$, so that $f$ is a probability density of values, this is the expected
revenue of the posted price $r$.

## Sources

- R. B. Myerson, "Optimal auction design", *Mathematics of Operations Research* 6(1) (1981), 58–73, §5, the single-bidder example.
