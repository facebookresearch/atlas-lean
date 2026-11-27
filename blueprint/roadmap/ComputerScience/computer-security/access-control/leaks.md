# A command leaks a right

The command `α` leaks the generic right `r` from the
configuration `Q`: run on `Q`, it can execute a primitive operation that enters `r` into a cell of
the access matrix that did not contain `r` just before. That is, for some actual parameters `x`
the condition of `α` holds in `Q`, and its body splits as `pre ++ op :: post` where the
operations of `pre` run from `Q` to some `Q₁` and `op` turns `Q₁` into some `Q₂` whose cell
`(s, o)` contains `r` while that of `Q₁` does not. The rest of the body need not be
executable.
