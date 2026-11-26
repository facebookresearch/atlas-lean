# Subst

Naive simultaneous substitution: each free occurrence of a name `x` that is a key of the
list `σ` is replaced by the value of the first pair with key `x`. A binder removes its names
from the list, and binders are never renamed.
