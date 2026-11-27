# Sharp scalar Lieb–Thirring bound on the line

Fix $1/2<\gamma<3/2$ and let $W\geq0$ almost everywhere in real $L^{\gamma+1/2}(\mathbb R)$. Use the complex form domain $H^1(\mathbb R)$ of $L^2$ functions with distributional derivative in $L^2$, with pairing $\langle v,u\rangle=\int\overline v u$ and form $q_W(v,u)=\int\overline{v'}u'-\int W\overline v u$. A weak eigenvector $u$ at negative energy $-k^2$ has $k>0$ and $q_W(v,u)=-k^2\langle v,u\rangle$ for all $v\in H^1$. Let $M_\gamma(W)$ be the extended nonnegative supremum of $\sum_i k_i^{2\gamma}$ over all finite orthonormal families of such vectors (including the empty one). Then $M_\gamma(W)\leq C_\gamma\int W^{\gamma+1/2}$, where

$$
C_\gamma=2\left(\frac{\gamma-1/2}{\gamma+1/2}\right)^{\gamma-1/2}\frac{\Gamma(\gamma+1)}{2\sqrt\pi\,\Gamma(\gamma+3/2)}.
$$

The supremum of the ratio over admissible $W$ with positive potential integral is $C_\gamma$, both using $M_\gamma$ and restricting to single normalized eigenvectors. The admissible potential $(r+1)\operatorname{sech}^2(rx)$, $r=(\gamma-1/2)^{-1}$, has positive potential integral and achieves equality in the full bound. This is scalar and does not classify other equality cases.

## Depends on
The weak eigenvalue equation on the entire Sobolev form domain, multiplicities counted by arbitrary finite orthonormal systems, and the gamma-function normalization of $C_\gamma$.

## Proof depends on
A sharp full-moment spectral inequality and explicit evaluation of the negative energy and potential integral for the stated well.

## Expansion
Separate the scalar one-state constant, saturation by the explicit potential, and the comparison of arbitrary finite families with the sharp constant. Pass to the extended-nonnegative supremum without assuming that the number of negative eigenvalues is finite.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/LiebThirring.lean#L92-L96) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/262.md).
