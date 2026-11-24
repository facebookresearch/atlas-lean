# Layer-cake formula for the truncated second moment

Let $\mu$ be a probability measure on $\mathbb{R}$ and let $x \ge 0$. With the [non-strict
absolute tail](tail-ge.md) $T_{\ge}(t) = \mu\{y : |y| \ge t\}$ and the [strict absolute
tail](tail-gt.md) $T_{>}(t) = \mu\{y : |y| > t\}$,

$$\int_{[-x, x]} y^2 \, d\mu(y) = 2 \int_0^x t\, T_{\ge}(t)\, dt - x^2\, T_{>}(x) .$$

The term $x^2 T_{>}(x)$ removes the contribution of the points with $|y| > x$, which lie outside
the closed truncation interval.
