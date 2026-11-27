# Generic discrete-logarithm game

Let `q > 1` and let `A` be a decision tree on three
labels with leaves in `ZMod q`. The game draws an encoding `enc` (a permutation of `ZMod q`) and a
secret `x ∈ ZMod q` uniformly and independently, runs `A` on the labels `enc 0`, `enc 1` and
`enc x` (of the identity, the generator and the target) with the oracle `oracleOf enc`, and
outputs `true` when `A` outputs `x`. Shoup's algorithm receives only the generator's and the
target's labels; the identity label gives the tree one more form than Shoup's game, hence the
`m + 3` in the bounds on this game where Shoup's proof has `m + 2`.

## Sources

- V. Shoup, *Lower Bounds for Discrete Logarithms and Related Problems*, revised version of the Eurocrypt 1997 paper, Section 2, Theorem 1.
