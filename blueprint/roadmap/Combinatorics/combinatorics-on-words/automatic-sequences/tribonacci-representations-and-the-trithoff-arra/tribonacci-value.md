# Tribonacci value of a digit word

Let $T_0 = T_1 = 0$, $T_2 = 1$ and
$T_{k+3} = T_{k+2} + T_{k+1} + T_k$ be the Tribonacci numbers. The Tribonacci value of a finite
word $w$ of natural-number digits $w_0, w_1, \dots, w_{\ell-1}$, listed from the least
significant digit, is $[w]_T = \sum_{i=0}^{\ell-1} w_i T_{i+3}$, so the digits weigh
$1, 2, 4, 7, 13, \dots$. Digits may exceed $1$ and three consecutive ones are allowed, so this
also evaluates the paper's non-canonical and improper representations.

For a Tribonacci representation $w$ of $n$, the value of $w$ followed by a new least
significant digit $0$ is the Tribonacci successor $\mathrm{out}(n)$.

## Sources

- E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4, Sections 2.3, 5 and 6.1.
