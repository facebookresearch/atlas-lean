# Bath Euler Residual

The actual residual of a computed temperature sequence `Y` in the Euler recurrence at
`dt = τ / 10`: `η_j = Y (j + 1) - (Y j + (τ / 10) Q(Y j) / C)`, the amount by which the computed
step `j` misses one exact Euler step. It is computed from `Y`, in the temperature unit of `Y`.
