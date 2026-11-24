# Finite-horizon dose budget

If the amount `A` satisfies,
for every `t`, the integral equation with finitely many dose
events at times `eventTime i`, all positive (`hevent`) of sizes `dose i` and
continuous elimination rate `k`, then on `[0, T]` the change in
amount is the included dose sum minus `k` times the integrated
amount. The initial dose is not counted: events are in `(0, T]`.
