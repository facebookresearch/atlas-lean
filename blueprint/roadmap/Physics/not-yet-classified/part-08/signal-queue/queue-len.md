# Queue Len

Deterministic fluid queue over one signal cycle: arrival rate
`lam`, service rate `mu`, red duration `R`. During red (`t ≤ R`)
the queue grows at rate `lam`; after red it drains at rate
`mu - lam` until it clears and then stays at zero. That draining
description is the physical regime `0 < lam < mu` with `0 ≤ R`,
which the results below assume; for general real parameters the
definition is the same totalized piecewise formula. Green
duration and cycle length are not parameters of `queueLen`: they
enter only through `queueLen_cycle_end`, where the green duration
is supplied explicitly.
