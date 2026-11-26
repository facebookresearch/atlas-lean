# Endpoint weak gradient of the centered disk maximal function

In Euclidean $\mathbb R^2$, write $Mf(x)=\sup_{r>0}(\pi r^2)^{-1}\int_{B(x,r)}|f(y)|\,dy$ using nonnegative integrals and extended values. A weak gradient $g$ of a real function $f$ satisfies $\int f\,\partial_i\varphi=-\int g_i\varphi$ for each coordinate $i$ and every real smooth compactly supported test function $\varphi$. There exists a real $C\geq0$ such that for every integrable $f$ and every integrable weak gradient $g$, $Mf$ is finite almost everywhere and its real representative (zero on the infinite locus) is locally integrable and in $W^{1,1}_{\rm loc}$. There is a globally integrable weak gradient $G$ of that representative with $\int |G|\leq C\int |g|$, using Euclidean vector norms. Local Sobolev membership means local integrability of the function and of a weak gradient.

## Depends on

- [Weak derivative convention](sobolev-embedding-theorem/is-weak-deriv.md), here with each Euclidean coordinate and all compactly supported smooth tests.

The centered averages are over open Euclidean disks, not squares or balls in the max norm.

## Proof depends on
- [Signed finite-band bound](signed-finite-band-centered-disk-gradient.md), for estimates uniform over the scale band on smooth inputs.

The limit also needs a finiteness estimate and a passage to weak gradients that preserves global integrability as the band exhausts all radii.

## Expansion

Separate the chain from signed smooth inputs to absolute averages, the approximation in $W^{1,1}$, and compactness or direct control of the weak gradients under the exhaustion. Prove almost-everywhere finiteness before using the real representative.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/DiskMaximal.lean#L56-L58) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/085.md).
