# Polynomially weighted binomial Fibonacci sums

Let $F_n$ denote the Fibonacci numbers,
$S(j, i)$ the Stirling numbers of the second kind and $(N)_i = N(N-1)\cdots(N-i+1)$ the falling
factorial. Let $A_0, A_1, A_2, \dots$ be complex numbers and $N$, $t$ natural numbers, and put
$h(y) = \sum_{j=0}^{t} A_j y^j$. Then

$$\sum_{k=1}^{N} h(k) \binom{N}{k} F_k =
\sum_{j=0}^{t} A_j \sum_{i=0}^{j} S(j, i)\, (N)_i\, F_{2N-i}.$$

Moreover,
$\sum_{k=1}^{N} (A_0 + A_1 k + A_2 k^2 + A_3 k^3 + A_4 k^4) \binom{N}{k} F_k$ equals
$A_0 F_{2N} + (A_1 + A_2 + A_3 + A_4) \binom{N}{1} F_{2N-1} +
2(A_2 + 3A_3 + 7A_4) \binom{N}{2} F_{2N-2} + 6(A_3 + 6A_4) \binom{N}{3} F_{2N-3} +
24 A_4 \binom{N}{4} F_{2N-4}$.

The source's hypotheses $N, t > 0$ and $t \le N/2$ are not needed and are dropped.

## Sources

- Andreea M. Stănică, Gabriela N. Stănică, and Pantelimon Stănică, *An Evaluation of Rationally Weighted Binomial Sums Via Some Differential and Integral Operators*, The Fibonacci Quarterly 62 (2024), Article 62-1/stanica09202023, Corollary 2.7.
