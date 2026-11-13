# Analytic expression of the Padovan–Perrin sequences

Let $k_1, k_2, p, s$ be natural
numbers with $k_1 > 0$, $p \ge 2$, $p < s$ and $k_1^2 < k_2$, let
$P(z) = z^{s+p} - k_1 z^p - k_2$, and let $v \colon \mathbb{N} \to \mathbb{C}$ satisfy
$v(n + s + p) = k_1 v(n + p) + k_2 v(n)$ for every $n$. For $0 \le m \le s + p - 1$ put
$A_m = k_2 v(m) + k_1 v(m + p)$ if $m < s$ and $A_m = k_2 v(m)$ if $m \ge s$. Then for every
$n \ge s + p$,

$$v(n) = \sum_{m=0}^{s+p-1} A_m \sum_{\lambda} \frac{\lambda^{n-1-m}}{P'(\lambda)},$$

where $\lambda$ runs over the complex roots of $P$ counted with multiplicity.

The paper assumes that the roots of $P$ are distinct; this follows from the other hypotheses
(Lemma 4 of the paper).

## Sources

- Elen Viviani Pereira Spreafico, Mustapha Rachidi, and Paula Maria Machado Cruz Catarino, *On a Model of (k;p;s)-Generalized Padovan-Perrin and Fibonacci Fundamental System*, INTEGERS 24 (2024), Article A49, Proposition 6.
