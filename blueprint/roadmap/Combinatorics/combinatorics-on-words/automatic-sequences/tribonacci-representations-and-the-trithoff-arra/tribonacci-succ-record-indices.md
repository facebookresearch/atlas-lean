# Indices used by records of the Tribonacci successor

Let $T_n$ be the Tribonacci numbers
($T_0 = T_1 = 0$, $T_2 = 1$, $T_{n+3} = T_{n+2} + T_{n+1} + T_n$) and let $\alpha$ be a real
number with $\alpha^3 = \alpha^2 + \alpha + 1$. For each $n$ fix a Tribonacci representation
$R(n) = (r_0, r_1, \dots, r_{\ell-1})$ of $n$: digits in $\{0, 1\}$ with no three consecutive
ones and $n = \sum_i r_i T_{i+3}$. Let $\mathrm{out}(n) = \sum_i r_i T_{i+4}$ be the Tribonacci
successor of $n$. Call $n$ a positive record if $n > 0$ and
$\mathrm{out}(m) - \alpha m < \mathrm{out}(n) - \alpha n$ for every $m < n$, and a negative
record if $n > 0$ and $\mathrm{out}(n) - \alpha n < \mathrm{out}(m) - \alpha m$ for every
$m < n$. If the digit $r_i$ of $R(n)$ equals $1$, then $T_{i+4} - \alpha T_{i+3} > 0$ when $n$
is a positive record, and $T_{i+4} - \alpha T_{i+3} < 0$ when $n$ is a negative record.

## Sources

- E. Chen et al., *Generalizing the Wythoff Array and Other Fibonacci Facts to Tribonacci Numbers*, Journal of Integer Sequences 28 (2025), Article 25.5.4, Proposition 4, part 1 and its negative analogue (`jis-2025-25.5.4-prop-4`).
