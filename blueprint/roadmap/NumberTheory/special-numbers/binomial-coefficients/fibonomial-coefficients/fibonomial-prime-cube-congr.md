# Kimball–Webb congruence for Fibonomial coefficients modulo $p^3$

Let $F_n$ be the
Fibonacci numbers, with $F_1 = F_2 = 1$, and write $F_n! = F_1 F_2 \cdots F_n$, with $F_0! = 1$.
Let $p \ge 7$ be a prime and $\varepsilon \in \{1, -1\}$, and suppose that $\rho = p - \varepsilon$
is the rank of appearance of $p$, that is, $p \mid F_\rho$ and $p \nmid F_m$ for $0 < m < \rho$.
Then for every natural number $k$ the Fibonomial coefficient

$$\binom{(k+1)\rho - 1}{\rho - 1}_F = \frac{F_{(k+1)\rho - 1}!}{F_{\rho - 1}!\, F_{k\rho}!}$$

is congruent to $\varepsilon^k$ modulo $p^3$.

The quotient is taken in the natural numbers; it is exact because Fibonomial coefficients are
integers. This is the Fibonacci case only, not Ballot's general theorem for Lucasnomial
coefficients.

## Sources

- Christian Ballot, *The Congruence of Wolstenholme for Generalized Binomial Coefficients Related to Lucas Sequences*, Journal of Integer Sequences 18 (2015), Article 15.5.4, <https://cs.uwaterloo.ca/journals/JIS/VOL18/Ballot/ballot14.tex>, Theorem `thm:KW` (rewriting Lemma 3 of Kimball and Webb), equation `eq:Fib`, lines 144-150.
