# Lineage-weight table of the proxy-substitution example

For a real number `α`, the proxy table gives seven populations, numbered `0` to `6`, weights on
eight edges, numbered `0` to `7`. Its rows are

- `0 = S₀`: `(1, 0, 0, 0, 0, 0, 0, 1)`;
- `1 = S₁`: `(0, 1, 1, 0, 0, 0, 0, 0)`;
- `2 = S₁'`: `(0, 1, 0, 1, 0, 0, 0, 0)`;
- `3 = T`: `(1 - α, α, α, 0, 0, 0, 0, 1 - α)`;
- `4 = R₀`: `(0, 0, 0, 0, 1, 0, 0, 0)`;
- `5 = R₁`: `(0, 1, 0, 0, 0, 1, 0, 0)`;
- `6 = R₂`: `(1, 0, 0, 0, 0, 0, 1, 0)`.

The table is defined for every real `α`. For `0 ≤ α ≤ 1` it lists the lineage weights of an
admixture graph: edge `0` is the stem shared by `S₀` and `R₂`, edge `1` the stem shared by `S₁` (the
true source), `S₁'` (a proxy splitting from the lineage of `S₁`) and `R₁`, edges `2` and `3` are
private to `S₁` and `S₁'`, edges `4`, `5`, `6` private to `R₀`, `R₁`, `R₂`, edge `7` private to
`S₀`, and the target `T` is the mixture `α S₁ + (1 - α) S₀`.
