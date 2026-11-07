# Ramanujan's integral formula with Bernoulli numbers

Let $f(-1, x) = 1$ and, for natural
numbers $n$, let $f(n, x) = e^{-x} \sum_{j=0}^{\infty} (j + 1)^n x^{j+1} / j!$ for complex $x$.
Let $B_n$ be the Bernoulli numbers, with $B_1 = -1/2$. Then for every natural number $m$ and every
complex number $x$,

$$\int_0^1 x\, f(m - 1, t x)\, dt = \sum_{k=0}^{m} \binom{m}{k} B_{m-k} \frac{f(k, x)}{k + 1}.$$

## Sources

- Berndt, Ramanujan's Notebooks Part I, Chapter 3, Section 8, Example 4 and its correction, printed pp. 51--52 / PDF pp. 61--62. Proves `Wanted` entry `ramanujan_part1_ch3_section8_example4_bernoulli_integral`.
