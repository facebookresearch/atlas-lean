# The query scan over children agrees with alpha-beta

For every leaf valuation $f$, side to move, window $(a, b)$ and list of shapes, the query
algorithm's scan over the children returns the same value as alpha-beta's scan over the children
instantiated by $f$, and makes exactly as many queries as that scan evaluates leaves.
