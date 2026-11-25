# Lineage-weight table of the reversed-direction example

For a real number `β`, the reversed table gives six populations, numbered `0` to `5`, weights on
eight edges, numbered `0` to `7`. Its rows are

- `0 = S₀`: `(1, 0, 0, 0, 0, 0, 0, 1)`;
- `1 = T`: `(0, 1, 1, 0, 0, 0, 0, 0)`;
- `2 = S₁`: `(1 - β, β, β, 1, 0, 0, 0, 1 - β)`;
- `3 = R₀`: `(0, 0, 0, 0, 1, 0, 0, 0)`;
- `4 = R₁`: `(0, 1, 0, 0, 0, 1, 0, 0)`;
- `5 = R₂`: `(1, 0, 0, 0, 0, 0, 1, 0)`.

The table is defined for every real `β`. For `0 ≤ β ≤ 1` it lists the lineage weights of an
admixture graph: edge `0` is the stem shared by `S₀` and `R₂`, edge `1` the stem shared by `T` and
`R₁`, edge `2` is private to the unadmixed target `T`, edge `3` private to `S₁`, edges `4`, `5`, `6`
private to `R₀`, `R₁`, `R₂`, and edge `7` private to `S₀`; the source `S₁` is the mixture
`β T + (1 - β) S₀` followed by drift on edge `3`.
