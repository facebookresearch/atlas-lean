# Filipponi's binomial-sum formula

For natural numbers $r$ and $s$ let
$f_r(s) = \sum_{j=0}^{s} \binom{r-j}{j}$, where $\binom{r-j}{j}$ is read as $0$ when $j > r$.
If $n$, $h$ and $k$ are natural numbers with $h \le n$ and $2k \le n - h$, then
$f_{n+2h}(k+h) = \sum_{j=0}^{h} \binom{h}{j} f_{n+j}(k+j)$.

The hypotheses encode the source condition $0 \le k \le (n-h)/2$; the identity also holds
without them.

## Sources

- Hacène Belbachir and Amine Belkhir, "Combinatorial Expressions Involving Fibonacci, Hyperfibonacci, and Incomplete Fibonacci Numbers", Journal of Integer Sequences 17 (2014), Article 14.4.3, lines 347–371 of <https://cs.uwaterloo.ca/journals/JIS/VOL17/Belbachir/belb2.tex>; the formula is attributed there to P. Filipponi (1996). Proves `Wanted` entry `filipponi_binomial_sum_formula`.
