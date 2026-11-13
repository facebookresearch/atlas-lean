# To Bits BE

The `w`-bit big-endian encoding of `n`: bit `i` of the list is bit `w - 1 - i` of `n`. Only
the low `w` bits of `n` are kept. Used to serialize integers as fixed-length strings, e.g. in
padded RSA and RSA-OAEP (Katz-Lindell, 2nd ed., §11.5).
