# Distinct elements needs Omega(1/eps^2 + log n) bits with constant failure probability

There is an absolute constant $c > 0$ such that for all $n$ and all $\varepsilon$ with $c/\sqrt{n} \le \varepsilon \le c$, every randomized one-pass streaming algorithm solving the $(\varepsilon, 1/3)$-distinct elements problem (output an estimate $\widetilde{F}_0$ of the number $F_0$ of distinct elements with $\Pr[\,|\widetilde{F}_0 - F_0| \le \varepsilon F_0\,] \ge 2/3$) on insertion-only streams over $[n]$ uses

$$
\Omega\big(\varepsilon^{-2} + \log n\big)
$$

bits of memory. Consequently the Kane–Nelson–Woodruff algorithm is space-optimal for constant failure probability.

## Proof sketch

The $\Omega(\log n)$ term holds already for constant-factor approximation and follows from the argument of Alon, Matias and Szegedy. For the $\Omega(\varepsilon^{-2})$ term, a streaming algorithm yields a one-way protocol: Alice streams the elements of her set, sends the memory, and Bob continues with his set, so that $F_0$ of the union determines the Hamming distance of the characteristic vectors. Distinguishing Hamming distance below $t/2 - \sqrt{t}$ from above $t/2 + \sqrt{t}$ for $t = \Theta(\varepsilon^{-2})$ needs $\Omega(t)$ bits of one-way randomized communication, proved through Yao's principle and a shatter-coefficient argument.

## Depends on

- [Turnstile streams, support size and linear sketches of a frequency vector](turnstile-streams-and-support-size.md)
- [Kane-Nelson-Woodruff distinct-elements algorithm with O(1/eps^2 + log n) bits](optimal-space-distinct-elements-algorithm.md)

## Proof depends on

- [Yao's minimax principle for communication complexity](../../../../TheoryOfComputation/communication-complexity/randomized-communication-protocols/rand-complexity-eq-i-sup-dist-complexity.md)

## Sources

- Noga Alon, Yossi Matias, Mario Szegedy, "The space complexity of approximating the frequency moments", J. Comput. Syst. Sci. 58 (1999).
- David P. Woodruff, "Optimal Space Lower Bounds for all Frequency Moments", SODA (2004).
