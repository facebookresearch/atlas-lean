# GTR identifiability from a single branch of known length

Let `ι` be a finite set of states. Write `Q(π, s)` for the
[GTR rate matrix](../time-reversible-nucleotide-substitution-models/gtr-rate.md) with base
frequencies `π` and exchangeabilities `s`: `Q(π, s) i j = s i j · π j` for `i ≠ j` and
`Q(π, s) i i = -∑_{k ≠ i} s i k · π k`. Let `(π, s)` and `(π', s')` lie in the
[GTR parameter domain](is-gtrparam.md) (`π i > 0`, `∑_i π i = 1`, `s` symmetric and `s i j > 0` for
`i ≠ j`, and likewise for `(π', s')`). If for one branch length `t > 0` the
[pair-site laws](gtr-pair-law.md) agree,
`π i · exp (t · Q(π, s)) i j = π' i · exp (t · Q(π', s')) i j` for all `i`, `j`, then `π = π'` and
`s i j = s' i j` for all `i ≠ j`. Fixing the branch length, for example by normalizing the expected
substitution rate, thus removes the rate/time symmetry.
