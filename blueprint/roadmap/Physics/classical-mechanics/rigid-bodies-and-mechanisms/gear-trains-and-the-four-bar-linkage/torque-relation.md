# Port torques of a gear train loaded only at its end shafts

For a gear train of `n` [meshes](mesh.md), `n ≥ 0`, with [train ratio](train-ratio.md) `R` and
[lossless meshes](is-lossless.md) for the port torques `a_k` and `b_k`, suppose the
[shaft load](shaft-load.md) `T_j` is `0` for every shaft `j` other than `0` and `n`. Then
`T₀ + R T_n = 0`; equivalently, the output torque is `T_n = -T₀ / R`, since
[`R ≠ 0`](train-ratio-ne-zero.md).
