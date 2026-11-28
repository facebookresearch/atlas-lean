# For positive lengths, workless force pairs are rod reactions

Let `l₁ > 0` and `l₂ > 0`, `q` a pair of angles and `p` the configuration given by the
[angle-to-position map](pos-map.md) at `q`. If a pair of forces `F` does no
[virtual work](virtual-work.md) along every pair of plane vectors in the kernel of the
[rod constraint Jacobian](rod-jacobian.md) at `p`, then there are unique multipliers `(c₁, c₂)` such
that `F` is the [rod reaction](rod-reaction.md) `(c₁ p₁ - c₂ (p₂ - p₁), c₂ (p₂ - p₁))`.
