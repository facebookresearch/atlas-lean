# Embedding preserves the output distribution

For every oracle `O` and computation `c`, evaluating `embed c` against
`withSampleOracle Smp O` gives the same output distribution as evaluating `c` against `O`.
