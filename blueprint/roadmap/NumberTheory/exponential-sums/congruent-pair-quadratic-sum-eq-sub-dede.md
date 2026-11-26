# Mittou's evaluation of a quadratic sum over congruent pairs

Let $p$ be a prime and $l$ a
positive integer with $\gcd(p, l) = 1$. Let $F(p, l)$ be the sum of
$\left(\frac{a}{p} - \frac{1}{2}\right)\left(\frac{b}{p} - \frac{1}{2}\right)$ over all pairs of
integers $a, b$ with $1 \le a, b \le p - 1$ and $b \equiv a l \pmod{p}$, and let

$$s(p, l) = \frac{1}{4l} \sum_{a=1}^{l-1} \cot\left(\frac{\pi a}{l}\right)
\cot\left(\frac{\pi a p}{l}\right)$$

be the Dedekind sum. Then

$$F(p, l) = \frac{p^2 - 3lp + l^2 + 1}{12 l p} - s(p, l).$$

Domain extension: the paper assumes $p \ge 3$; the identity also holds for $p = 2$ (then $l$ is
odd and both sides vanish), so that hypothesis is dropped. The paper's remark that $s(p, l)$
depends only on $p \bmod l$ is not restated.

## Sources

- Brahim Mittou, *Explicit Evaluation of a Quadratic Sum Over Congruent Pairs Modulo a Prime*, INTEGERS 25 (2025), Article A85, Theorem 1.
