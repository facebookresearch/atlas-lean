# Abel's variant of Klamkin's identity

For real numbers $c$ and $d$ write
$\binom{c}{d} = \Gamma(c+1) / (\Gamma(d+1) \, \Gamma(c-d+1))$; for natural numbers this is the
usual binomial coefficient. Let $a$ and $b$ be real numbers such that $-a$ and $-b$ are not in
$\{0, 1, 2, \dots\}$ and $a - b$ is not an integer, and let $n \ge 1$ be a natural number with
$n < -a - 1$. Then the series

$$\sum_{k \ge 0} (-1)^k \binom{n+k-1}{k} \binom{a}{b+k}^{-1}$$

converges unconditionally to $\frac{a+1}{a+n+1} \binom{a+n}{b}^{-1}$.

Abel assumes only $a - b + 1 \notin \mathbb{N}$; here $a - b$ must avoid every integer, since
otherwise some $\Gamma(a - b - k + 1)$ is evaluated at a pole of $\Gamma$.

Proof: Rewrite the summand as an ordinary hypergeometric coefficient and apply Abel's
specialization of Gauss's formula (Abramowitz-Stegun 15.1.20), then simplify by Gamma recurrence.

## Sources

- Ulrich Abel, "A Short Proof of the Binomial Identities of Frisch and Klamkin," Journal of Integer Sequences 23 (2020), Article 20.7.1, Theorem (label theorem-variant-Klamkin), equation (Identity-variant-Klamkin), lines 210–218, https://cs.uwaterloo.ca/journals/JIS/VOL23/Abel/abel12.tex
