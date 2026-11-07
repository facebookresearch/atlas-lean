# Liouville's divisor-function identity

For every positive integer $n$, writing $\tau(d)$
for the number of positive divisors of $d$,

$$\left(\sum_{d \mid n} \tau(d)\right)^2 = \sum_{d \mid n} \tau(d)^3,$$

where both sums run over the positive divisors $d$ of $n$.

## Sources

- Seon-Hong Kim and Kenneth B. Stolarsky, “Translations and Extensions of the Nicomachean Identity,” Journal of Integer Sequences 27 (2024), lines 317–322, `https://cs.uwaterloo.ca/journals/JIS/VOL27/Kim/kim8.tex` (full TeX SHA-256 `787b1d5e48f218f3b44166059063c4be564a15df0ed18d8793b2aed240aecb1f`; exact quoted span SHA-256, including its terminal LF, `5b7c9a7479bb8eb08ba025ed7f94848fd6abef52db394974d3dca55292110351`). Here `d.divisors.card` is the source's divisor-count function. It follows from `liouville_divisor_function_identity_general`; the hypothesis `hn` is unused and keeps the source's shape (at `n = 0` both sides are `0`, since `Nat.divisors 0 = ∅`). Proves `Wanted` entry `liouville_divisor_function_identity`.
