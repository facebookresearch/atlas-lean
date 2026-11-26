# Homogeneous-coordinate form of Nagata’s inequality

For every integer $r\ge10$, there exist countably many proper closed sets of ordered distinct $r$-tuples of complex projective-plane points, with nonempty common complement. Closed means cut out by multihomogeneous equations restricted to the distinct configurations. For each tuple $p$ outside these sets, each $d\ge1$, each nonzero homogeneous ternary polynomial $F$ of degree $d$, and each natural-number vector $(m_i)$, assume that in every coordinate chart containing $p_i$ the dehomogenization of $F$ belongs to the $m_i$-th power of the affine point ideal of $p_i$. Then $\sum_i m_i<d\sqrt r$. The exceptional sets do not depend on $d,F$ or the multiplicity vector.

## Depends on

- Projective configurations and multihomogeneous vanishing; [affine ordinary multiplicity](multiplicity.md) and its chartwise ideal-power form.

## Proof depends on

- The very-general strict degree bound on simultaneous vanishing-order constraints, including a nonempty exceptional complement.

## Expansion

Build the incidence loci for fixed degree and multiplicity vector, prove properness for the excluded vectors using the cited polynomial bound, and combine them countably. Compare this coordinate statement with the effective-cycle statement via the homogeneous-equation and multiplicity bridges.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/Nagata.lean#L365-L367) and [its definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/Nagata.lean).
