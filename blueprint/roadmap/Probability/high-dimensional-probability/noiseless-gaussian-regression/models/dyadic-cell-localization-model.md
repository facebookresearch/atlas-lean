# Dyadic cell disclosures and Gaussian block localization

The initial coordinate cube in dimension $n$ is $[-1/(2\sqrt n),1/(2\sqrt n))^n$ with normalized volume. Level-$J$ cells are the half-open subcubes of side $1/(\sqrt n\,2^J)$ indexed by coordinate indices in $[2^J]^n$. The root is level zero. For localization chart a point $z$ to $(z,\sqrt{1-\|z\|^2})$, use independent Gaussian rows of width $\lfloor n/16\rfloor$, and feed exact labels to the finite-state block rule. A disclosure at each block is a measurable finite-range cell label that contains the actual point for every history, nested as the history is extended. At a positive horizon its final level is the level of the last disclosed cell, and at zero it is zero. In the finite-entropy regularization model, a strict descendant is heavy when its conditional mass exceeds $2^{-n\Delta J/2}$; first-heavy means no other heavy ancestor below the starting cell. Use volume conditioned on the cell as its uniform reference. These cell definitions do not depend on a Gaussian projection density.

## Sources

- [Pinned model definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GaussianInformation.lean#L11-L94)
- [Pinned model definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GaussianFiniteEntropy.lean#L10-L31)
- [Pinned model definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/GaussianFiniteEntropy.lean#L103-L182)
