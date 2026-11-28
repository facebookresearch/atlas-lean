# GTR identifiability from a single branch, up to rate/time scaling

Let `ι` be a finite set of states. Write `Q(π, s)` for the
[GTR rate matrix](../../time-reversible-nucleotide-substitution-models/gtr-rate.md) with base
frequencies `π` and exchangeabilities `s`: `Q(π, s) i j = s i j · π j` for `i ≠ j` and
`Q(π, s) i i = -∑_{k ≠ i} s i k · π k`. Let `(π, s)` and `(π', s')` lie in the
[GTR parameter domain](is-gtrparam.md) (`π i > 0`, `∑_i π i = 1`, `s` symmetric and `s i j > 0` for
`i ≠ j`, and likewise for `(π', s')`). Let `t > 0` and `t' > 0` be branch lengths. The
[pair-site laws](gtr-pair-law.md) `F(π, s, t) i j = π i · exp (t · Q(π, s)) i j` and `F(π', s', t')`
are equal if and only if `π = π'` and the branch-scaled exchangeabilities agree off the diagonal:
`t · s i j = t' · s' i j` for all `i ≠ j`. Thus one branch identifies the base frequencies and the
products `t · s i j`, and nothing more: the only symmetries are the
[rate/time scaling](gtr-pair-law-smul.md) `(π, c · s, t) ~ (π, s, c · t)` and the unused diagonal of
`s`. This is a statement about the law, not about estimators.
