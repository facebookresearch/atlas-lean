# Settling Guarantee

The supplied analog settling model. The observed voltage is the
ideal voltage plus additive noise. Whenever the resolution time is
within the budget, the ideal voltage encodes the expected bit in its
output band (`Vol` on the low side, `Voh` on the high side) and the
noise is below both noise margins formed from `Vol < Vil` and
`Vih < Voh`. No claim is made outside the stated budget.
