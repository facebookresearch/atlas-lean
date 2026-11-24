# Valid two-channel chain

A [two-channel chain](two-channel.md) with rates `rate₁, rate₂` and targets `target₁, target₂` is
valid if, for every state `x`:

- its rates are nonnegative: `rate₁ x ≥ 0` and `rate₂ x ≥ 0`;
- a channel whose jump would not move the chain has rate `0`: `rate₁ x = 0` if `target₁ x = x`,
  and `rate₂ x = 0` if `target₂ x = x`.

There is no condition on the target `target₁₂` of simultaneous jumps.
