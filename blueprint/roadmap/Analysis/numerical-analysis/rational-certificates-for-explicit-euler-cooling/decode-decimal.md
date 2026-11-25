# Bounded decimal decoding

A list of characters decodes to a natural number when it has between $1$ and $11$ characters, all ASCII decimal digits; the result is computed by Horner's rule, $n \mapsto 10n + v(c)$ over the characters from the most significant, starting from $0$. Otherwise (empty, longer than eleven characters, or containing a non-digit) the result is none.
