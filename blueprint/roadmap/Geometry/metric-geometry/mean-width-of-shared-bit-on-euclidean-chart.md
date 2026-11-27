# Shared-bit price on a convex Euclidean chart is normalized mean width

Let $K$ be any field and $X$ a metric space satisfying the [CAT(0) comparison](spectral-placement-prices-and-cat-zero-segments.md). Fix a spectral placement price $P$ over $K$ on $X$ as defined there.

Use its diagonal price on finite sets of occupied sites. Assume the source's synchronized convexity for the price of this binary diagonal: for every finite nonempty slot type and two placements $p,q$ on it, the price at the slotwise interpolation on the chosen comparison segments at $t\in[0,1]$ is at most $(1-t)$ times the price at $p$ plus $t$ times the price at $q$. Placements here may repeat sites; this is not a hypothesis only about injective maps.

Let $E$ be a finite-dimensional real inner-product space with Borel structure, $C\subset E$ convex, and $e:E\to X$ distance-preserving on pairs of points of $C$. For every nonempty finite $S\subset C$, the diagonal price on $e(S)$ equals

$$
\sqrt{2\pi}\int_E \max_{x\in S}\langle u,x\rangle\,d\gamma_E(u),
$$

where $\gamma_E$ is the standard Gaussian measure. The support maximum is that of the convex hull of $S$; the normalization assigns a segment its Euclidean length. The chart need not be open or the whole space. This does not assert the corresponding infinite-dimensional Hilbert-space extension.

## Depends on

- [Spectral placement prices and CAT(0) segments](spectral-placement-prices-and-cat-zero-segments.md), synchronized binary-diagonal convexity, and the normalized Gaussian support integral.

## Proof depends on

- Diagonal monotonicity, intersecting submodularity, the spectral two-site and triangle bounds, and the Euclidean rigidity argument for a price with these properties. The Euclidean chart transports geodesic convexity to affine convexity.

## Expansion

Port the placed tensor semiring/price structure and the metric interpolation law. Separate the spectral diagonal identities from the Gaussian support integral and the local-to-global Euclidean price law; prove the chart statement for all convex charts, not only those with ambient interior.

## Sources

- OpenAI, [Finite tensor formats and restriction](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/LinearAlgebra/SpectralBooks/SiteTensor/Raw.lean#L19-L46), [normalized spectrum](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/LinearAlgebra/SpectralBooks/Spectrum.lean#L18-L23), [grouping and full spectral placement price](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/LinearAlgebra/SpectralBooks/SpectralSpace.lean#L20-L63).
- OpenAI, [Synchronized convexity and chart theorem](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/LinearAlgebra/SpectralBooks/SpectralFlatLaw.lean#L37-L112), [Diagonal price](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/LinearAlgebra/SpectralBooks/SpectralDiagonal.lean#L18-L30), and [Support function](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/LinearAlgebra/SpectralBooks/Width.lean#L24-L33), [Gaussian normalization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/LinearAlgebra/SpectralBooks/Width.lean#L59-L73).
