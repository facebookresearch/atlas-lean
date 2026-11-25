# Valiant's Bernoulli-trial bound, $L(h, S) \le \lceil 2h(S + \ln h) \rceil$

Let $X_0, \dots, X_{m-1}$ be independent random variables with values in $\{0, 1\}$ (Bernoulli
trials), each with success probability $P(X_i = 1) \ge 1/h$, where $h > 1$ is real, and let
$S \ge 1$ be an integer. If $m \ge 2h(S + \ln h)$, then

$$P\Big(\sum_{i<m} X_i < S\Big) < \frac{1}{h}.$$

In Valiant's notation, $L(h, S)$ is the least number of such trials after which fewer than $S$
successes has probability less than $1/h$. Since $L(h, S)$ is an integer, the statement gives
$L(h, S) \le \lceil 2h(S + \ln h) \rceil$. Valiant's Proposition, the single probabilistic lemma
behind his learning algorithms, is the slightly sharper $L(h, S) \le 2h(S + \ln h)$, that is, the
same bound already at $\lfloor 2h(S + \ln h) \rfloor$ trials; the argument below does not reach
that case for $h$ close to $1$.

Valiant's proof uses a Chernoff bound on the binomial lower tail. The proof here instead applies
the exponential Markov inequality at $t = -1$: with $N = \sum_i X_i$,

$$P(N < S) \le e^{S}\,\mathbb{E}[e^{-N}] = e^{S} \prod_i \big(1 - (1 - e^{-1}) P(X_i = 1)\big)
\le e^{S} e^{-(1 - e^{-1}) m / h} < e^{S} e^{-m/(2h)} \le \frac{1}{h},$$

using independence, $1 - x \le e^{-x}$ and $1 - e^{-1} > 1/2$.

## Sources

- L. G. Valiant, *A theory of the learnable*, Communications of the ACM 27 (1984), 1134-1142, Section 4, Proposition.
