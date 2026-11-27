# Real time G(y) exceeds t exactly when standard time y exceeds R(t)

Let `ρ`, `t` and `y` be nonnegative real numbers. Let `G` be the [time change](growth-time.md)
for exponential growth at rate `ρ` and let `R(t) = ∫_0^t exp(ρ r) dr` be the
[cumulative coalescence intensity](../site-frequency-spectrum-under-variable-populatio/cum-rate.md)
of the [relative size](exp-growth-size.md) `η(r) = exp(-ρ r)`. Then

`t < G(y)` if and only if `R(t) < y`.

An event at standard time `y` happens at real time `G(y)`; it happens after the real time `t`
exactly when `y` exceeds the intensity accumulated by real time `t`.
