# Fisher time reversal

Swapping the two periods (base/current, with baskets
swapped accordingly) gives the reciprocal index: the forward and reversed Fisher indices
multiply to `1`. The hypothesis is that all four basket values are strictly positive, so
every ratio is well defined and every square root is of a positive number. This follows
from ratio cancellation (`div_mul_div_cancel₀'`) and square-root product identities
(`Real.sqrt_mul`).
