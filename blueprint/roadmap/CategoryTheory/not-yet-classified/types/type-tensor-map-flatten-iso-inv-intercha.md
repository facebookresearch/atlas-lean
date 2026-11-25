# Type Tensor Map flatten Iso inv interchange

Interchange, inv direction: pushing a nested reindexing family
map through `flattenIso.inv`. Uncurrying the mapped nested element
at a reindexed flattened index equals the component map applied to
the uncurried input. This is the direction consumed by
`graftEvaluationIso`, whose flatten head is `flattenIso.inv`.
