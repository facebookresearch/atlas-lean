# Tingley extension of a surjective sphere isometry

Let $X$ and $Y$ be nonzero real Banach spaces and put $S_X=\{x\in X:\|x\|=1\}$ and $S_Y=\{y\in Y:\|y\|=1\}$, with the metrics induced by the original norms. If $f:S_X\to S_Y$ is a surjective isometry, there exists a real-linear isometric equivalence $T:X\to Y$ with all of the following properties:

- $T(u)=f(u)$ for every $u\in S_X$;
- $T(0)=0$ and $T(x)=\|x\| f(x/\|x\|)$ for every $x\ne 0$;
- $T$ is surjective;
- every real-linear map $L:X\to Y$ that agrees with $f$ on $S_X$ equals the underlying linear map of $T$. No continuity or isometry hypothesis is imposed on $L$.

## Depends on

- [Normed vector space](../../normed-spaces/normed-space.md)

## Proof depends on

- Vanishing of the two-point distance defect of the radial map, globally on the pair of ambient spaces, not just on the two unit spheres.
- Linearity of an onto isometry of real normed spaces that carries zero to zero (Mazur–Ulam).

## Expansion

Define the radial map by the two cases above. Establish its surjectivity by choosing a preimage of $y/\|y\|$ for $y\ne 0$. Separate the two-point defect estimate, its positive-defect attainment in an ultrapower, and the chord/alignment argument that rules out a positive attained defect. Once the ambient distance identity is available, package the radial map as a linear isometric equivalence and prove uniqueness by scaling an arbitrary nonzero vector from the sphere; use linearity at zero.

## Sources

- OpenAI, [Comparator statement and normalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/TingleySphereIsometry.lean#L10-L36).
- OpenAI, [scope and accompanying paper](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/322.md).
