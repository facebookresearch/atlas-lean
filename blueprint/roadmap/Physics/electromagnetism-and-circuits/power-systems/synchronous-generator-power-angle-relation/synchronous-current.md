# Generator current in the synchronous machine model

For real `E`, `V`, `X_s` and `δ`, the generator current is `I = (E e^(iδ) - V) / (i X_s)`: the
internal voltage phasor `E e^(iδ)` at load angle `δ` minus the terminal voltage phasor `V`, taken as
the real reference, divided by the purely reactive impedance `i X_s`. The current is directed out of
the generator toward the bus, and the model is lossless. In the model the internal voltage magnitude
`E`, the terminal voltage magnitude `V` and the synchronous reactance `X_s` are positive. With the
convention `z / 0 = 0` for complex division, the current is `0` when `X_s = 0`.
