# Rate and time are confounded at a single branch

Let `ι` be a finite set of states. Write `Q(π, s)` for the
[GTR rate matrix](../../time-reversible-nucleotide-substitution-models/gtr-rate.md) with base
frequencies `π` and exchangeabilities `s`: `Q(π, s) i j = s i j · π j` for `i ≠ j` and
`Q(π, s) i i = -∑_{k ≠ i} s i k · π k`. For all real `π`, `s`, `c` and `t`, the exchangeabilities
`c · s` over time `t` give the same
[transition matrix](../../../../Probability/markov-chains/finite-continuous-time-markov-chains/the-transition-semigroup-of-a-finite-continuous/ctmc-transition.md)
as `s` over time `c · t`: `exp (t · Q(π, c · s)) = exp ((c · t) · Q(π, s))`. So a transition matrix
observed at one unknown branch length cannot separate the branch length from the scale of `s`; at
most the products `t · s i j` can be identified.
