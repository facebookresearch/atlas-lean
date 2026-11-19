# Velocity formula for the (a, b)-knight

Let $a$ and $b$ be natural numbers with
$1 \le a < b$, $\gcd(a, b) = 1$ and $a + b$ odd, let
$N_{a,b} = \{(\pm a, \pm b), (\pm b, \pm a)\}$ be the $(a,b)$-knight's move set, and for
$p \in \mathbb{Z}^2$ let $d_{a,b}(p)$ be the piece distance of $p$ for $N_{a,b}$. For a natural
number $h$, let $B_h = \{(x, y) \in \mathbb{Z}^2 : \max(|x|, |y|) \le h\}$ be the max-norm
ball and let $\bar{d}(h) = |B_h|^{-1} \sum_{p \in B_h} d_{a,b}(p)$ be the average of $d_{a,b}$
over $B_h$. Then

$$\lim_{h \to \infty} \frac{2h}{3} \, \bar{d}(h)^{-1} = \frac{2(a+b)b^2}{a^2 + 3b^2}.$$

## Sources

- Christian Táfula, *Knights Are 24/13 Times Faster than the King*, The Fibonacci Quarterly 62(3) (2024), Theorem 1.3.
