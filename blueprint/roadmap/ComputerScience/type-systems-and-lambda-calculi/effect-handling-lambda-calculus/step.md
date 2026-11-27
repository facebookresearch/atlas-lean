# Small-step semantics

β-reduction of applications, conditionals, `do` after `return`,
the return clause of a handler, and the handler rule: in `with h handle E[op o v]`, where `h` is
a handler literal whose first clause for `o` (found by `List.lookup`) is `c`, and no handler of
`E` handles `o`, the step goes to `c[v/x, κ/k]` with the continuation
`κ = fun y ↦ with h handle E[return y]`, which re-installs the handler (Hillerström-Lindley
2016, Fig. 7). Inside `κ` the handler and the context are shifted past the bound `y`. Steps are
closed under `do` frames and under handler frames with a handler literal; under
`with h handle …` for any other value `h`, such as a variable, nothing steps
(Pretnar 2015, Fig. 3).
