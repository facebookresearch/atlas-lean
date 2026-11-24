# Two-bus current-limited power flow example

The example has two buses joined by one branch from bus `0` to bus `1` with admittance `1` and no
shunts; active demands `0` and `15/16`, reactive demands `0`; active generation limits `[-2, 3]` at
bus `0` and `[0, 0]` at bus `1` (no active generation there); reactive generation limits `[-1, 1]`;
squared voltage magnitudes in `[1/8, 4]`; squared current limit `4`; and cost coefficients `1` at
bus `0` and `0` at bus `1`, so generation is paid at bus `0` only. It is a
[current-limited AC optimal power flow problem](../current-limited-ac-optimal-power-flow-and-its-vo/current-limited-opf.md).
