# Partial map from branching types to session types

Fix a passive sort `passive` in a sort type with decidable equality. The partial map from branching types to payload-free session types keeps `end` and the sends and receives whose payload sort is `passive`, and returns `none` on every `select` or `branch` choice and on every send or receive at a sort other than `passive`.
