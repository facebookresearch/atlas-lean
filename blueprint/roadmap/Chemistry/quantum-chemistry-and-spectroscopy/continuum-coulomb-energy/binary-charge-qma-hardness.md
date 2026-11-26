# QMA-hardness of continuum electronic energy with binary nuclear charges

For every bit-string promise problem with a [verifier in the stated promise class](coulomb-promise-and-verifiers.md), there exists a many-one reduction with the stated deterministic polynomial-time stack-machine certificate to the stated continuum Coulomb energy promise. It outputs a nonempty list of distinct rational positions with positive **binary** integer charges, a positive **unary** electron count, and lower and upper binary-encoded rational thresholds $a,b$ with $b-a\ge1$. Yes outputs satisfy $E\le a$ and no outputs $E\ge b$, where $E$ is the same extended-real form infimum over the full normalized spinful antisymmetric continuum domain. The polynomial bound covers the complete encoded output, not the numerical magnitudes of the charges.

## Depends on

- [Encoding, form-domain and verifier conventions](coulomb-promise-and-verifiers.md)

## Expansion

Check the binary-charge reduction's yes/no energy inequalities with the continuum form, and bound all output encodings including the unary electron field. Alternatively, verify a polynomial-time encoding lift from the unit-charge result: insert the code for charge one at each existing position, prove validity and exact equality of the normalized energy infima, then compose reductions.

## Sources

- OpenAI, [Comparator statement and definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ContinuumCoulombHardness.lean#L454-L550) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/275.md).
- OpenAI, [Continuum Coulomb hardness with binary nuclear charges](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Continuum-Coulomb-hardness-with-binary-nuclear-charges-September-24-2026/Continuum-Coulomb-hardness-with-binary-nuclear-charges-September-24-2026.pdf) (September 24, 2026), accompanying preprint. The comparator above specifies the selected formal scope.
