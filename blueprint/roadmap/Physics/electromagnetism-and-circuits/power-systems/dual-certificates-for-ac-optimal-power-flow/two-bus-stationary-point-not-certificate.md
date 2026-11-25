# A stationary point with matching bound is not a certificate

For the [two-bus example](two-bus-cert-example.md), the voltage `V = (2, 3/4)` and the
[stationarity multipliers](two-bus-stationary-multipliers.md):

- `V` is [AC feasible](../current-limited-ac-optimal-power-flow-and-its-vo/ac-feasible.md);
- the [dual slack](dual-slack.md) `S` of the multipliers satisfies `S V = 0` (the Lagrangian is
  stationary at `V`);
- the [AC cost](../current-limited-ac-optimal-power-flow-and-its-vo/ac-cost.md) of `V` is `5/2`,
  equal to the [certified lower bound](certified-lower-bound.md) of the multipliers;
- the multipliers fail the [sign check](nonneg.md);
- `S` is not `F Fᴴ` for any complex matrix `F` of any width;
- the certified optimum `(2, 5/4)` has AC cost `3/2 < 5/2`.

So stationarity with a matching would-be bound does not certify optimality.
