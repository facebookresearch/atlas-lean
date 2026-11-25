# Ideal lossless meshes of a gear train

For a gear train of `n` [meshes](mesh.md), `n ≥ 0`, and port torques `a_k` (applied to mesh `k` by
its upstream shaft) and `b_k` (applied by its downstream shaft), signed about the common axis
direction, the train is lossless when `a_k w + b_k (r_k w) = 0` for every mesh `k` and every real
`w`, where `r_k` is the [signed ratio](ratio.md) of mesh `k`: no mesh absorbs power on any motion
`(w, r_k w)` of its two shafts allowed by its no-slip constraint. The torques may have either sign,
so power may enter a mesh through either shaft.
