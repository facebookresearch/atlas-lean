# Rational generator-to-bus incidence matrix

For finitely many buses and generators placed at buses, the rational generator incidence has entry
`1` at bus `v` and generator `g` when `g` is at `v`, and `0` otherwise. The rational objects copy
the real ones entrywise, so that the checker is computable; the
[casting lemmas](rat-lp-matrix-map.md) identify them with the real linear program.
