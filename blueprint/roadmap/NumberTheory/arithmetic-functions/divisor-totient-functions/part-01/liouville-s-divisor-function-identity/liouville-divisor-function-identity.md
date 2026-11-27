# Liouville's divisor-function identity

For every positive integer $n$, writing $\tau(d)$
for the number of positive divisors of $d$,

$$\left(\sum_{d \mid n} \tau(d)\right)^2 = \sum_{d \mid n} \tau(d)^3,$$

where both sums run over the positive divisors $d$ of $n$.

## Sources

- Seon-Hong Kim and Kenneth B. Stolarsky, “Translations and Extensions of the Nicomachean Identity,” Journal of Integer Sequences 27 (2024), lines 317–322, <https://cs.uwaterloo.ca/journals/JIS/VOL27/Kim/kim8.tex>. Here `d.divisors.card` is the source's divisor-count function. It follows from `liouville_divisor_function_identity_general`; the hypothesis `hn` is unused and keeps the source's shape (at `n = 0` both sides are `0`, since `Nat.divisors 0 = ∅`).
