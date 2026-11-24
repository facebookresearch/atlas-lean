# Net Port Power flipped secondary current

The entering-current sign is essential: keep `I2` the entering
secondary current but give it the erroneous sign relation
`I2 = n * I1` (the relation a leaving secondary current would
satisfy), with `V1 = n * V2`. The entering-power sum
`netPortPower (n * V2) I1 V2 (n * I1)` is then `2 * (n * V2 * I1)`,
not zero in general: power conservation fails for the wrong
entering sign. This lemma does not reinterpret `I2` as a leaving
current; with a leaving current the entering-power formula itself
would be `V1 * I1 - V2 * I2`, a different function.
