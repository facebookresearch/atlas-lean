# Alternating binomial sum of Fibonacci numbers

Let $F_m$ denote the $m$-th Fibonacci
number, with $F_0 = 0$ and $F_1 = 1$. For all natural numbers $n$ and $k$,

$$\sum_{i=0}^{n} (-1)^i \binom{n}{i} F_{2n-i+k} = F_k.$$

## Sources

- Brian Hopkins and Aram Tangboonduangjit, "Scaled Fibonacci- and Lucas-Producing Rational Polynomials," Journal of Integer Sequences 25 (2022), Article 22.3.5 (Corollary generalizing Corollary cor51(a), lines 989–1000), <https://cs.uwaterloo.ca/journals/JIS/VOL25/Hopkins/tang25.tex>. The sum is the `n`-th forward difference, which telescopes by Pascal's rule and `fib (m + 2) = fib m + fib (m + 1)`. Proves `Wanted` entry `binomial_fibonacci_convolution`.
