# Variance block Contrast

Variance of the weighted block contrast under independent complete
randomization within each block: it is the sum over blocks of the squared
weight `((blocks b).card / N) ^ 2` (`N = Fintype.card ι`) times that block's
exact Neyman variance `popVar y₁ / n b + popVar y₀ / ((blocks b).card - n b) -
popVar (y₁ - y₀) / (blocks b).card`, with population variances taken on the
block subtype. Each block needs at least one treated and one control unit
(`h₁`, `h₀`); no disjointness or coverage assumption on the blocks is
required.
