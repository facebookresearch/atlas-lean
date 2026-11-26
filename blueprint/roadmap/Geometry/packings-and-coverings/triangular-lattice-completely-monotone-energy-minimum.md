# Universal energy minimum for the density-one triangular lattice

Let $b=\sqrt3/2$ and $A=b^{-1/2}\{(j+k/2,bk):j,k\in\mathbb Z\}\subset\mathbb R^2$. Suppose every intersection $C_R=C\cap\overline B(0,R)$ is finite and $|C_R|/(\pi R^2)\to1$ as $R\to\infty$. Let $g:\mathbb R\to\mathbb R$ be smooth on $(0,\infty)$ and satisfy $g(t)\geq0$ and $(-1)^k g^{(k)}(t)\geq0$ for all integers $k\geq0$ and $t>0$. Define

$$
E_g(C)=\liminf_{R\to\infty}\frac{1}{|C_R|}\sum_{x\in C_R}\sum_{y\in C_R\setminus\{x\}}g(|x-y|^2).
$$

Use extended nonnegative values, with the empty-disk expression zero and pairs ordered. Then $\sum_{a\in A\setminus\{0\}}g(|a|^2)\leq E_g(C)$ and $E_g(A)=\sum_{a\in A\setminus\{0\}}g(|a|^2)$. Divergent energies are allowed; no neutralizing background or separation assumption is included.

## Depends on
Centered closed-disk density, ordered off-diagonal energy, and the covolume-one lattice. Complete monotonicity concerns squared distance and only positive arguments.

## Proof depends on

- [Sharp Gaussian minorants](triangular-gaussian-minorants-with-atomic-construction.md), providing the Gaussian comparison.

A positive Gaussian-mixture route for completely monotone potentials and the centered-disk Gaussian energy comparison at density one.

## Expansion

Separate the Gaussian finite-window and boundary estimates from the positive mixture passage. Pass through a lower-limit inequality in extended nonnegative values without assuming finite energy, and separately prove lattice attainment by the limiting frequencies for fixed off-origin displacements.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/TriangularEnergy.lean#L65-L70) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/090.md).
