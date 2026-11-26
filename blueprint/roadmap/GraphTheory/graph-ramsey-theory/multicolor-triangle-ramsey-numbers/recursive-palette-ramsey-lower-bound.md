# Ramsey lower bound from a recursive palette construction

Let $H,a$ be natural numbers with $H\ge2$, $a\ge2$, and $\log H\le a$, where the logarithm is natural. Put $w=\lceil 2H\log H\rceil$, $s=w(w+1)+1$, and $q=Has$. Then the multicolor triangle Ramsey number satisfies

$$ R_q(3)\ge (H/e^4)^q. $$

The power and the comparison are in the reals, with natural exponent $q$. This bound applies at the specified color count, not automatically to all larger counts with the same exponent.

## Depends on

- [Multicolor triangle Ramsey number](multicolor-triangle-ramsey-number.md)

## Proof depends on

- [Recursive separated-palette colorings](recursive-separated-palette-colorings.md)

## Expansion

Separate the recursive construction of a triangle-free coloring from its order estimate. The construction must reach stage $H$ with $Has$ colors. Combine the finite order estimate with the factorial and logarithmic inequalities that give the stated constant $e^4$.

## Sources

- [Pinned recursive palette lower bound](https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/MulticolorTriangleRamsey.lean#L2159-L2165)
