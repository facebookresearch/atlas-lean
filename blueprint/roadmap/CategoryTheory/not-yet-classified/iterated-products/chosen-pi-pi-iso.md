# Chosen Pi Pi Iso

Canonical isomorphism from the independently chosen flat product to the independently
chosen iterated product.

The three product choices are taken as independent typeclass arguments, fixing the gap in
Mathlib's `piPiIso` which induces its sigma product internally. Both inverse laws are
proved by `Pi.hom_ext` and the projection simp lemmas.
