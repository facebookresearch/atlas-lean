# The two-bus relaxed point is feasible but not a voltage lift

For the [two-bus example](two-bus-cert-example.md), the [relaxed point](two-bus-relaxed-point.md)
`W = [[4, 2], [2, 17/16]]` is
[relaxation feasible](../current-limited-ac-optimal-power-flow-and-its-vo/sdp-feasible.md), is not
the lift `V Vᴴ` of any voltage vector `V`, and has
[relaxation cost](../current-limited-ac-optimal-power-flow-and-its-vo/sdp-cost.md) `2`, strictly
above the certified bound `3/2` of the [two-bus witness](two-bus-certificate.md). The certificate
bounds it without recovering a voltage from it.
