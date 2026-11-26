# Substitution Factors Inner Index

The inner index in the substitution-factor family attached to `i : X.index`.

It corresponds to `some i` in the underlying `Option` indexing type, but is
provided with the exact bundled-family index type
`((substitutionFactors O).obj X).index` so that clients need not spell the
semireducible `Option` implementation.
