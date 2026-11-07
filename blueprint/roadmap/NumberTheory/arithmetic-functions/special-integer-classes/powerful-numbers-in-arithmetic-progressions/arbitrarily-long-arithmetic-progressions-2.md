# Arbitrarily long arithmetic progressions of powerful numbers

For every integer $k \ge 3$
there are positive integers $a$ and $d$ such that each of the $k$ numbers $a + id$ with
$0 \le i < k$ is powerful: every prime that divides $a + id$ has its square dividing $a + id$.

## Sources

- Tsz Ho Chan, "Arithmetic Progressions Among Powerful Numbers", Journal of Integer Sequences 26 (2023), Article 23.1.1, Theorem `thm-longAP`, source lines 97–99, <https://cs.uwaterloo.ca/journals/JIS/VOL26/Chan/chan33.tex>. The paper notes the result is not new (see remark 2 in [H] there) and includes a proof for completeness. Powerful (squarefull) means every prime divisor appears with exponent at least two; nonconstant is `0 < d`. It follows from `arbitrarily_long_arithmetic_progressions_of_powerful_numbers_general`, which states powerfulness as `Nat.IsKFull 2`; the hypothesis `hk` is unused and keeps the source's shape. Proves `Wanted` entry `arbitrarily_long_arithmetic_progressions_of_powerful_numbers`.
