# A digit run decodes exactly when well formed, to its positional value

For a list of characters `d` and a natural number `n`, the
[bounded decimal decoder](decode-decimal.md) returns `n` on `d` if and only if `d` is a
[run of one to eleven decimal digits](is-decimal-digits.md) and `n` is its
[positional value](decimal-value.md).
