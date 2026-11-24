# Decoding one trace token

For a list of characters, the token decoder [splits](split-on-char.md) it at `/`; when there are
exactly two pieces, a [numerator](decode-numerator.md) `z` and a
[denominator](decode-denominator.md) `d` that both decode, it returns the rational `z / d` (the
denominator being at least `1`); otherwise it returns nothing.
