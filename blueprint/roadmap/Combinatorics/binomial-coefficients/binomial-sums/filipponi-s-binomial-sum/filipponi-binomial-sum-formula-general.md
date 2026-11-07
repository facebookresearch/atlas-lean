# Filipponi's binomial-sum formula, without range conditions

For natural numbers $r$
and $s$ let $f_r(s) = \sum_{j=0}^{s} \binom{r-j}{j}$, where $\binom{r-j}{j}$ is read as $0$ when
$j > r$. Then for all natural numbers $n$, $h$ and $k$,
$f_{n+2h}(k+h) = \sum_{j=0}^{h} \binom{h}{j} f_{n+j}(k+j)$.

The source states the formula under the condition $0 \le k \le (n-h)/2$; with the convention
above it holds for all $n$, $h$ and $k$.

## Sources

- Hacène Belbachir and Amine Belkhir, "Combinatorial Expressions Involving Fibonacci, Hyperfibonacci, and Incomplete Fibonacci Numbers", Journal of Integer Sequences 17 (2014), Article 14.4.3, definition of `f_r(s)` at lines 304–319 and the formula at lines 347–371 of <https://cs.uwaterloo.ca/journals/JIS/VOL17/Belbachir/belb2.tex> (file SHA-256 `e60c0875f28ac5be72af638a5a6d955c789993dfeed0f463afbb34955be8f2fe`, extracted statement text SHA-256 `c34b4ffa5811994595d796e20d6310141e9e6214ad20c93468c26bf2bc1233db`); the formula is attributed there to P. Filipponi, "Incomplete Fibonacci and Lucas numbers", Rend. Circ. Mat. Palermo 45 (1996), 37–56, DOI 10.1007/BF02845088. Stable task identifier `jis_grounded_1b088a32a9d82c1527d97e03__filipponi_binomial_sum_formula`.
