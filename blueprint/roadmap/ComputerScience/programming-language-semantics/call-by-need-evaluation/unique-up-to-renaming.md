# Unique up to renaming

Evaluation is deterministic up to renaming of new names. If a configuration is closed with
respect to `A`, then any two of its evaluations perform the same number of additions, and a
permutation fixing every name of `A` and every name bound in `Γ` maps the final heap and value
of the first evaluation to those of the second. Without closedness this fails: a free name
bound neither in the heap nor in `A` can collide with a new name.
