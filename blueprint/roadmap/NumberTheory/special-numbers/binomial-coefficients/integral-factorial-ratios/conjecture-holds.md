# Erdős Problem 728 holds: factorial divisibility with a logarithmic excess

There is a real number $\delta > 0$ such that for every real number
$\varepsilon$ with $0 < \varepsilon < \delta$ and all real numbers $C > 0$ and $C' > C$, there are
natural numbers $a$, $b$ and $n \ge 1$ with $a > \varepsilon n$, $b > \varepsilon n$,
$a! \, b! \mid n! \, (a + b - n)!$ and $n + C \log n < a + b < n + C' \log n$.

Barreto and ChatGPT-5.2 proved that for any $0 < C_1 < C_2$ there are infinitely many
$a, b, n$ with $b = n/2$, $a = n/2 + O(\log n)$, $C_1 \log n < a + b - n < C_2 \log n$ and
$a!\,b! \mid n!\,(a+b-n)!$, which resolves the statement above in the affirmative.

## Sources

- Erdős Problem #728, https://www.erdosproblems.com/728 (the resolution by Barreto and ChatGPT-5.2).
- Nat Sothanaphan, *Resolution of Erdős Problem #728: a writeup of Aristotle's Lean proof*, arXiv:2601.07421 (2026), https://arxiv.org/abs/2601.07421.
- P. Erdős, R. L. Graham, I. Z. Ruzsa and E. G. Straus, *On the prime factors of $\binom{2n}{n}$*, Mathematics of Computation 29 (1975), 83–92, p. 91.
