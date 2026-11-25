# Lineage-weight table of the ghost-source example

For a real number `α`, the ghost table gives seven populations, numbered `0` to `6`, weights on
eight edges, numbered `0` to `7`. Its rows are

- `0 = S₀`: `(1, 0, 0, 0, 0, 0, 0, 0)`;
- `1 = S₁`: `(0, 1, 0, 1, 0, 0, 0, 0)`;
- `2 = G`: `(0, 1, 1, 0, 1, 0, 0, 0)`;
- `3 = T`: `(1 - α, α, α, 0, α, 0, 0, 0)`;
- `4 = R₀`: `(0, 0, 0, 0, 0, 1, 0, 0)`;
- `5 = R₁`: `(0, 1, 1, 0, 0, 0, 1, 0)`;
- `6 = R₂`: `(0, 1, 1, 0, 0, 0, 0, 1)`.

The table is defined for every real `α`. For `0 ≤ α ≤ 1` it lists the lineage weights of an
admixture graph: edge `0` is private to `S₀`, edge `1` the stem shared by `S₁`, `G`, `R₁` and `R₂`,
edge `2` the continuation shared by `G`, `R₁` and `R₂`, edges `3` and `4` are private to `S₁` and
`G`, edges `5`, `6`, `7` private to `R₀`, `R₁`, `R₂`, and the target `T` is the mixture
`α G + (1 - α) S₀` of the true source `G`, which is not sampled as a source, and `S₀`.
