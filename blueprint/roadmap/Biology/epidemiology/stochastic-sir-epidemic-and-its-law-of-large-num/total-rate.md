# Total rate of a two-channel chain

For a [two-channel chain](two-channel.md) with rates `rate₁, rate₂`, the total rate at a state `x`
is

`rate₁ x + rate₂ x`.

For a [valid](is-valid.md) chain it is the total rate of jumps out of `x`, and it is `0` exactly
when neither channel is active. For arbitrary real rates it is only their sum, which can be `0`
while the rates are not, as for the rates `1` and `-1`.
