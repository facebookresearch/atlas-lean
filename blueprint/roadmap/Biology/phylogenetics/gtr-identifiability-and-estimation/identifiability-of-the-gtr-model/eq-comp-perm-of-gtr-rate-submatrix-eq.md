# GTR identifiability from the rate matrix up to relabeling

Let `ι` be a finite set of states. Write `Q(π, s)` for the
[GTR rate matrix](../../time-reversible-nucleotide-substitution-models/gtr-rate.md) with base
frequencies `π` and exchangeabilities `s`: `Q(π, s) i j = s i j · π j` for `i ≠ j` and
`Q(π, s) i i = -∑_{k ≠ i} s i k · π k`. Let `(π, s)` and `(π', s')` lie in the
[GTR parameter domain](is-gtrparam.md) (`π i > 0`, `∑_i π i = 1`, `s` symmetric and `s i j > 0` for
`i ≠ j`, and likewise for `(π', s')`). If, for a permutation `σ` of the states,
`Q(π, s) (σ i) (σ j) = Q(π', s') i j` for all `i`, `j`, so that the rate matrix of `(π, s)` is
observed only up to the unknown relabeling `σ`, then the parameters are determined up to the same
relabeling: `π' i = π (σ i)` for every `i` and `s' i j = s (σ i) (σ j)` for all `i ≠ j`. For `σ` the
identity this is the forward implication of
[GTR identifiability from the rate matrix, exact form](gtr-rate-eq-iff.md).
