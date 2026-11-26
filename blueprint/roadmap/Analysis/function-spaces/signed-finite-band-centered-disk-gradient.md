# Signed finite-band centered disk maximal gradient bound

Let $f:\mathbb R^2\to\mathbb R$ be smooth and compactly supported. For real $a>0$ and integer $m\geq0$ set $S_{a,m}f(x)=\sup_{a\leq r\leq 2^m a}(\pi r^2)^{-1}\int_{B(x,r)}f(y)\,dy$. Both ends are included, including the singleton band at $m=0$, and the average has no absolute value on $f$. There is one real $C\geq0$ independent of $a,m,f$ such that $S_{a,m}f$ is locally integrable and has an integrable weak gradient $G$ with $\int |G|\leq C\int |\nabla f|$. Weak gradient means $\int S_{a,m}f\,\partial_i\varphi=-\int G_i\varphi$ for all smooth compactly supported real test functions and each coordinate.

## Depends on

- [Weak derivative convention](sobolev-embedding-theorem/is-weak-deriv.md).

The supremum is a real supremum of signed averages over a nonempty compact interval of positive radii.

## Proof depends on

Control of the maximizers of the continuous-radius family and a gradient bound that does not accumulate with the number of dyadic scales.

## Expansion

Separate differentiation of a disk average, the active-radius gradient formula including endpoint maximizers, and the planar estimate integrating that gradient uniformly in $m$. Verify the singleton-radius boundary case and keep the signed convention.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/SignedFiniteBand.lean#L45-L47) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/085.md).
