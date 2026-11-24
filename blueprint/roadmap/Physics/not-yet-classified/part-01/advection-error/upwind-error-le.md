# Upwind error le

Finite error induction: if `u` solves the same upwind recurrence on the same periodic nodes
with `0 ≤ ν ≤ 1`, the nodal error `E_k = maxⱼ |u_j^k - w_j^k|` satisfies
`E_N ≤ E_0 + N * (dt * M * (v² dt + v dx) / 2)`.
