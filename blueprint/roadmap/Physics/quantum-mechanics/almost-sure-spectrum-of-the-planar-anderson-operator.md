# Almost-sure spectrum of the planar Anderson operator

Fix $h>0$. On $\mathbb Z^2$ choose independent real site potentials $V_{i,j}$ with common law $\operatorname{Leb}|_{[-h,h]}/(2h)$. The proposed spectral equality is for almost every entire configuration under this product law. For such a configuration there is a bounded self-adjoint operator $H$ on $\ell^2(\mathbb Z^2;\mathbb C)$ with

$$
(Hu)_{i,j}=u_{i+1,j}+u_{i-1,j}+u_{i,j+1}+u_{i,j-1}+V_{i,j}u_{i,j}
$$

for every $u$ and every site, and its spectrum in the complex bounded-operator algebra is exactly $\{z\in\mathbb C:\operatorname{Im}z=0,\ -4-h\le \operatorname{Re}z\le4+h\}$. The same operator satisfies both the coordinate formula and the spectral equality. The hopping convention is the adjacency operator, **not** the Laplacian shifted by a diagonal constant. Equality of the spectral set does not state pure point spectral type, eigenfunction decay, or localization. The potential law is uniform, not Bernoulli.

## Proof depends on

- [Bounded self-adjoint realization](anderson-operator-exists-ae.md)
- [Approximate eigenvalues belong to the spectrum](../../Analysis/operator-theory/spectral-theory/approximate-point-spectrum/mem-spectrum-of-is-approximate-eigenvalu.md)
- [Spectrum of a bounded self-adjoint operator](../../Analysis/operator-theory/spectral-theory/spectrum-of-self-adjoint-operators/self-adjoint-spectrum-subset-icc.md)

## Expansion

For the upper inclusion, bound the norm of each translation by one and that of the diagonal multiplier by $h$. For the reverse inclusion, first prove that for each tolerance and side length, disjoint trials almost surely include a box where all potentials approximate a fixed interior value. Choose a countable family of tolerances, lengths and potential levels to get one full-measure event. Cut off plane waves on these boxes, estimate the boundary error relative to the norm, and use approximate eigenvalues and closedness of the spectrum to include both endpoints.

## Sources

- OpenAI, [Comparator statement and definitions](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PlanarAndersonSpectrum.lean#L11-L29) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/261.md).
- OpenAI, [Pure-Point Spectrum for the Two-Dimensional Anderson Model at Every Positive Disorder](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/preprints/Pure-Point-Spectrum-for-the-Two-Dimensional-Anderson-Model-at-Every-Positive-Disorder-September-23-2026/paper.pdf) (September 23, 2026), accompanying preprint. The comparator above specifies the selected formal scope.
