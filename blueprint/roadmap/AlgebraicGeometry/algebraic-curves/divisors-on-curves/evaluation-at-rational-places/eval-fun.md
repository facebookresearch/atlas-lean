# Eval Fun

Evaluation of a divisor of places supported on rational places against a
function-field element: the product over the divisor of the values of the
element at each place, raised to the divisor coefficient at that place.

The value is multiplicative in the divisor only where the element has nonzero
values. If `f` has the value `0` at `v` (a zero of `f`, or a pole, where
`Place.evalAt` gives `0`), then `[v]` and `-[v]` both evaluate to `0`, since
`0⁻¹ = 0`, while their sum evaluates to `1`. `WeilReciprocity` evaluates each of
its two nonzero functions only on the divisor of the other, whose support
carries none of its zeros or poles.
