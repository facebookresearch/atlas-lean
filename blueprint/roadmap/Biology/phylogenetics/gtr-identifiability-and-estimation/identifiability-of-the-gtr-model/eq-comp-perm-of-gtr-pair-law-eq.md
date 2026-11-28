# Single-branch identifiability up to relabeling and rate/time scaling

Let `ι` be a finite set of states. Write `Q(π, s)` for the
[GTR rate matrix](../../time-reversible-nucleotide-substitution-models/gtr-rate.md) with base
frequencies `π` and exchangeabilities `s`: `Q(π, s) i j = s i j · π j` for `i ≠ j` and
`Q(π, s) i i = -∑_{k ≠ i} s i k · π k`. Let `(π, s)` and `(π', s')` lie in the
[GTR parameter domain](is-gtrparam.md) (`π i > 0`, `∑_i π i = 1`, `s` symmetric and `s i j > 0` for
`i ≠ j`, and likewise for `(π', s')`). Let `t > 0` and `t' > 0` be branch lengths and `σ` a
permutation of the states. If the [pair-site law](gtr-pair-law.md)
`F(π, s, t) i j = π i · exp (t · Q(π, s)) i j` of `(π, s, t)` is observed only up to the relabeling
`σ`, `F(π, s, t) (σ i) (σ j) = F(π', s', t') i j` for all `i`, `j`, then `π' i = π (σ i)` for every
`i` and `t' · s' i j = t · s (σ i) (σ j)` for all `i ≠ j`.
