# Bounded decoding of a decimal digit run

For a list of characters, the decoder returns, when the list has one to eleven characters and each
is a decimal digit, the natural number obtained by Horner's rule `n ↦ 10 n + v(d)` over the
characters from the first, with `v` the [digit value](digit-value.md); otherwise it returns nothing.
