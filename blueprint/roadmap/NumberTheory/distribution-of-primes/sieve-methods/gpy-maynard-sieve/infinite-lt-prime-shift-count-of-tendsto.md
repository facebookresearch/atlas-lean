# From the asymptotics of $S_1$ and $S_2$ to infinitely many prime-rich translates

Let $w_N(n) \ge 0$ and set

$$S_1(N) = \sum_{N \le n < 2N} w_N(n), \qquad S_2(N) = \sum_{N \le n < 2N} \Bigl(\sum_{h \in H} \mathbf 1_{\mathbb P}(n + h)\Bigr) w_N(n).$$

If $B(N) > 0$ for all large $N$, $S_1(N)/B(N) \to I$, $S_2(N)/B(N) \to J$ and $\rho I < J$, then infinitely many $n$ have more than $\rho$ of the $n + h$ prime.

This is the limiting step of the proof of Proposition 4.2 in Maynard (2015): $S = S_2 - \rho S_1$ is eventually positive because $(S_2 - \rho S_1)/B \to J - \rho I > 0$, display (4.4). Maynard's sums (4.2)–(4.3) also restrict $n$ to a residue class $v_0 \bmod W$; here that restriction is part of the weights $w_N$. No sign condition on $I$ is needed.

The hypotheses can hold non-trivially: with $H = \{0\}$, $w_N(n) = \mathbf 1_{\mathbb P}(n)$ and $B = S_1$, which is positive for $N \ge 2$ by Bertrand's postulate, both ratios are eventually $1$ and the conclusion is the infinitude of the primes.

## Informally uses

- [GPY detection principle over dyadic ranges](infinite-lt-prime-shift-count-of-eventua.md): applied to $S_2 - \rho S_1$.

## Sources

- J. Maynard, "Small gaps between primes", *Ann. of Math.* 181 (2015), 383–413; theorem and display numbers are those of arXiv:1311.4600v3 (28 Oct 2019).
