# To Rat? eq

For a value `f` of the core binary64 model, the exact rational value `toRat? f` is read off its unpacked form: it is `none` for NaN and for either infinity, `some 0` for either signed zero, and `some (sm · 2^e)` for a finite value with sign `s`, mantissa `m` and exponent `e`, where `sm` is the mantissa `m` with the sign `s` applied.
