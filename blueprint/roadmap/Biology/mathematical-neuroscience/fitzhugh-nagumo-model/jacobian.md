# Jacobian matrix of the FitzHugh–Nagumo field

For real `b`, `ε` and `v`, the Jacobian matrix at a state with voltage `v` is

`J = [[1 - v², -1], [ε, -ε b]]`,

with rows for the voltage and recovery components and columns for `∂/∂v` and `∂/∂w`. Its entries are
the [partial derivatives of the field](jacobian-eq-partials.md) at every state `(v, w)`; it does not
depend on `a`, `I` or `w`.
