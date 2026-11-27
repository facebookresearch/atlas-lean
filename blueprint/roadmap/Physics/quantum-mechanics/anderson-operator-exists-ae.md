# Almost-sure existence of the planar Anderson operator

Let $h>0$ and sample the
values $V_{i,j}$ independently and uniformly in $[-h,h]$. For almost every configuration $V$,
there is a bounded self-adjoint operator $H$ on $\ell^2(\mathbb Z^2;\mathbb C)$ with

$$
(Hu)_{i,j}=u_{i+1,j}+u_{i-1,j}+u_{i,j+1}+u_{i,j-1}+V_{i,j}u_{i,j}
$$

for every $u$ and every site $(i,j)$. This assertion specifies the operator, not its spectrum.

## Sources

- OpenAI, [square-lattice Anderson model, bounded realization](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/MathematicalPhysics/PlanarAnderson/Spectrum.lean#L179-L208), the existence and self-adjointness part of the [Comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PlanarAndersonSpectrum.lean#L11-L28).
