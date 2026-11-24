# Top Pair Completion Cost merge third Last le

CPython's third-last choice is the tree rotation
`A + (B + C) -> (A + B) + C`.  Under its exact guard `|A| < |C|`, paying for
that rotation and then canonically completing cannot cost more than the
paper's top-pair completion.
