# Partial map from branching types to protocols

Fix a passive sort in a sort type with decidable equality. The partial map from branching types to protocols first applies the partial map to payload-free session types at that passive sort and then converts the resulting finite session type to a protocol; it is `none` exactly where the first map is.
