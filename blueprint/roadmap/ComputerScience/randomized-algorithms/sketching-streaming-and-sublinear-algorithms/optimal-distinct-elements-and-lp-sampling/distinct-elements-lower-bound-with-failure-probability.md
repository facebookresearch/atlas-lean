# Omega(eps^-2 log(1/delta)) lower bounds for distinct elements and Johnson-Lindenstrauss with failure probability delta

There are absolute constants $c, C > 0$ such that the following hold whenever $0 < \varepsilon, \delta < c$ and the universe size $n$ (respectively the dimension $d$) is at least $(\varepsilon^{-2}\log(1/\delta))^{C}$.

1. Every randomized one-pass algorithm solving the $(\varepsilon, \delta)$-distinct elements problem (output an estimate $\widetilde{F}_0$ of the number $F_0$ of distinct elements with $\Pr[\,|\widetilde{F}_0 - F_0| \le \varepsilon F_0\,] \ge 1 - \delta$) on insertion-only streams over $[n]$ uses $\Omega(\varepsilon^{-2}\log(1/\delta) + \log n)$ bits.
2. Every probability distribution over linear maps $\Pi : \mathbb{R}^d \to \mathbb{R}^k$ such that $\Pr[\,|\|\Pi x\|_2^2 - \|x\|_2^2| \le \varepsilon\|x\|_2^2\,] \ge 1 - \delta$ for every fixed $x \in \mathbb{R}^d$ has $k = \Omega(\varepsilon^{-2}\log(1/\delta))$.

In particular the median of $O(\log(1/\delta))$ independent constant-error repetitions is optimal in its $\varepsilon$ and $\delta$ dependence, but the multiplicative blow-up of the $\log n$ term is not forced.

## Proof sketch

Both bounds come from augmented indexing over an alphabet $U$ of size $\Theta(1/\delta)$: Alice holds $x \in U^N$, Bob holds a prefix of $x$ and one more symbol $y_i$, and must decide whether $x_i = y_i$. An information-cost argument with Fano's inequality shows that every one-way protocol with error $\delta$ has information cost, hence communication, $\Omega(N\log(1/\delta))$. An encoding with a shared random string maps instances of length $N = \Theta(\varepsilon^{-2})$ (or $N = \Theta(\varepsilon^{-2}\log n)$) into gap instances of Hamming distance, so that distinguishing the two cases needs a $(1 \pm \Theta(\varepsilon))$-estimate. For distinct elements, Alice streams the ones of her encoded vector, sends the memory, and Bob continues with his, so that $F_0$ determines the Hamming distance; this gives $\Omega(\varepsilon^{-2}\log(1/\delta))$, and the $\Omega(\log n)$ term holds already for constant error. For linear maps, the parties share $\Pi$ through public coins, Alice sends $\Pi x$ rounded to $O(\log n)$ bits per entry, and the public-coin bound $\Omega(\varepsilon^{-2}\log n\log(1/\delta))$ for estimating the Euclidean distance of the encoded vectors gives $k = \Omega(\varepsilon^{-2}\log(1/\delta))$.

## Depends on

- [Turnstile streams, support size and linear sketches of a frequency vector](turnstile-streams-and-support-size.md)

## Proof depends on

- [Distinct elements needs Omega(1/eps^2 + log n) bits with constant failure probability](distinct-elements-space-lower-bound.md)
- [Yao's minimax principle for communication complexity](../../../../TheoryOfComputation/communication-complexity/randomized-communication-protocols/rand-complexity-eq-i-sup-dist-complexity.md)

## Sources

- T. S. Jayram, David P. Woodruff, "Optimal Bounds for Johnson-Lindenstrauss Transforms and Streaming Problems with Sub-Constant Error", SODA (2011); ACM Trans. Algorithms (2013).
