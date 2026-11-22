# Reduction LTS decorated with barb observations

The decorated reduction system of the π-calculus is the labelled transition system on processes, with the [labels](behaviour-label.md) for reductions and observations, in which $P$ has a reduction transition to $Q$ when $P \to Q$ ([reduction](../the-calculus-syntax-substitution-structural-cong/step.md)), and an observation transition labelled $o$ to $Q$ when $Q = P$ and $P$ has the [barb](barb.md) $o$. Observation transitions consume no prefix and transmit no name.
