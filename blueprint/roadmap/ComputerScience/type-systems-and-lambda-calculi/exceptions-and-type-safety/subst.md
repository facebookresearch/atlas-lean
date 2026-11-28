# Parallel substitution in a term

Given a substitution `σ` assigning a term to each de
Bruijn index, substituting `σ` into a term replaces each free variable `i` by `σ i`; under the
binder of an abstraction body or of a handler the substitution is lifted, sending `0` to the
variable `0` and `i + 1` to `σ i` with every free variable raised by one.
