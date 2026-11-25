# GTR identifiability from the rate matrix, exact form

Let `ι` be a finite set of states. Write `Q(π, s)` for the
[GTR rate matrix](../time-reversible-nucleotide-substitution-models/gtr-rate.md) with base
frequencies `π` and exchangeabilities `s`: `Q(π, s) i j = s i j · π j` for `i ≠ j` and
`Q(π, s) i i = -∑_{k ≠ i} s i k · π k`. Let `(π, s)` and `(π', s')` lie in the
[GTR parameter domain](is-gtrparam.md) (`π i > 0`, `∑_i π i = 1`, `s` symmetric and `s i j > 0` for
`i ≠ j`, and likewise for `(π', s')`). Then `Q(π, s) = Q(π', s')` if and only if `π = π'` and
`s i j = s' i j` for all `i ≠ j`: the rate matrix determines the parameters exactly, up to the
diagonal of `s`, which it does not use.
