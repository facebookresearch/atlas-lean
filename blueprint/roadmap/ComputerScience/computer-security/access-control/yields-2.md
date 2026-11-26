# Running a command

The relation `Q ⊢_{α(x₁, …, x_k)} Q'` of Harrison, Ruzzo and Ullman:
running the command `α` with the actual parameters `x` on the configuration `Q` gives `Q'`. If
the condition of `α` fails in `Q`, then `Q' = Q`. Otherwise `Q'` is the end of a run
`Q ⇒_{op₁*} Q₁ ⇒ ⋯ ⇒_{opₙ*} Q'` of the body with the actual parameters substituted for the formal
ones; if some operation of the body cannot be executed, there is no such `Q'`.
