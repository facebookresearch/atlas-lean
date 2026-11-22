# Delta-hedging wealth tracks the claim value at every node

Along every history of length at most `N`, the self-financing delta-hedging strategy started
with the backward-induction value `claimValue u d R V N []` has wealth equal to the claim value at
that node.
