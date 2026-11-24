# Grounded DC load-flow solve and flow transfer

For positive susceptances on a connected
network, a reference node, and balanced injections `p`:

1. the grounded angles (reduced grounded matrix solve, `θ ref = 0`) are the unique `θ` with
   `θ ref = 0` and `L_b θ = p`;
2. they vanish at the reference and solve `L_b θ = p`;
3. their DC injection `B f`, with `f = diag(b) Bᵀ θ` for the same `B` and `b`, is `p`;
4. their branch flows are `b e * (θ tail - θ head)`, and every solution of `L_b θ = p` carries the
   same flows;
5. the DC model's per-line bound holds at the grounded angles:
   `|P e - f e| ≤ b e * |θ tail - θ head| ^ 3 / 6`.
