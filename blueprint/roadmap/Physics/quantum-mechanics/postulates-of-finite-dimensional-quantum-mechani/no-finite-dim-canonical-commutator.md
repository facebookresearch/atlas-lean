# No finite-dimensional canonical commutation relation

For `0 < n` and `ħ ≠ 0`, no
complex `n × n` matrices `X`, `P` satisfy `X * P - P * X = I • ħ • 1`. Proof by the trace
argument: the trace of a commutator vanishes (`Matrix.trace_sub`, `Matrix.trace_mul_comm`),
while the trace of the scalar matrix is `n * (I * ħ) ≠ 0` (`Matrix.trace_smul`,
`Matrix.trace_one`). This is why position and momentum need unbounded operators with explicit
domains; no infinite-dimensional statement is made here.
