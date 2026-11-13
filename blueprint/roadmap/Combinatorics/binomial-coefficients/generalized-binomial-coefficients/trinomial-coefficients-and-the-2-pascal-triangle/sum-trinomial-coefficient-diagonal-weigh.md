# Weighted diagonal sums of trinomial coefficients by coefficient extraction

Write
$\binom{n}{k}_2$ for the trinomial coefficient, the coefficient of $t^k$ in $(1+t+t^2)^n$,
$[t^m]\,g$ for the coefficient of $t^m$ in a power series $g$, and $f_k = [t^k]\,f$. For every
integer $n > 0$ and every formal power series $f \in \mathbb{Q}[[t]]$

$$\sum_{k=0}^{\lfloor 2n/3 \rfloor} \binom{n-k}{k}_2 \frac{n}{n-k} f_k =
[t^{2n}]\, \frac{(1-t+t^2)^{n-1}(3-4t+2t^2)}{1-t}\,
f\!\left(\frac{t^3}{(1-t+t^2)(1-t)}\right).$$

## Sources

- Yassine Otmani, *The 2-Pascal Triangle and a Related Riordan Array*, Journal of Integer Sequences 28 (2025), Article 25.3.5, Theorem 32 (`jis-2025-25.3.5-thm-32`).
