# Omega(eps^-2 log(1/delta)) lower bounds for distinct elements and Johnson-Lindenstrauss with failure probability delta

There are absolute constants $c, C > 0$ such that the following hold whenever $0 < \varepsilon, \delta < c$ and the universe size $n$ (respectively the dimension $d$) is at least $(\varepsilon^{-2}\log(1/\delta))^{C}$.

1. Every randomized one-pass algorithm solving the $(\varepsilon, \delta)$-distinct elements problem (output an estimate $\widetilde{F}_0$ of the number $F_0$ of distinct elements with $\Pr[\,|\widetilde{F}_0 - F_0| \le \varepsilon F_0\,] \ge 1 - \delta$) on insertion-only streams over $[n]$ uses $\Omega(\varepsilon^{-2}\log(1/\delta) + \log n)$ bits.
2. Every probability distribution over linear maps $\Pi : \mathbb{R}^d \to \mathbb{R}^k$ such that $\Pr[\,|\|\Pi x\|_2^2 - \|x\|_2^2| \le \varepsilon\|x\|_2^2\,] \ge 1 - \delta$ for every fixed $x \in \mathbb{R}^d$ has $k = \Omega(\varepsilon^{-2}\log(1/\delta))$.

In particular the median of $O(\log(1/\delta))$ independent constant-error repetitions is optimal in its $\varepsilon$ and $\delta$ dependence, but the multiplicative blow-up of the $\log n$ term is not forced.

## Proof sketch

Both bounds come from a one-way communication problem: an augmented version of approximate Hamming distance in which Bob must decide whether the distance is small or large, for $\log(1/\delta)$ independent instances embedded at different scales, with overall error $\delta$. An information-complexity argument shows that the one-way information cost of this problem is $\Omega(\varepsilon^{-2}\log(1/\delta))$. A streaming algorithm or a linear embedding that succeeds with probability $1 - \delta$ would solve the problem with communication equal to its memory or to $k$ times the word size, giving the stated bounds.

## Depends on

- [Turnstile streams, support size and linear sketches of a frequency vector](turnstile-streams-and-support-size.md)

## Proof depends on

- [Distinct elements needs Omega(1/eps^2 + log n) bits with constant failure probability](distinct-elements-space-lower-bound.md)
- [Yao's minimax principle for communication complexity](../../../../TheoryOfComputation/communication-complexity/randomized-communication-protocols/rand-complexity-eq-i-sup-dist-complexity.md)

## Sources

- T. S. Jayram, David P. Woodruff, "Optimal Bounds for Johnson-Lindenstrauss Transforms and Streaming Problems with Sub-Constant Error", SODA (2011); ACM Trans. Algorithms (2013).
