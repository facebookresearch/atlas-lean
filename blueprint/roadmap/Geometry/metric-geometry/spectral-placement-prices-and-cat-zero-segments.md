# Spectral placement prices and CAT(0) segments

## Spectral placement prices

Fix a field $K$ and a pseudometric space $X$. A placed tensor has a finite slot type $I$, a finite basis $B_i$ at each slot, an array of coefficients in $K$ on the product of these bases, and a placement $x:I\to X$. Write $D_I$ for the binary common diagonal with one basis vector for each bit at each slot. Its coefficient at a binary label tuple is the number, in $K$, of common labels producing that tuple. The price is real-valued on placed tensors and satisfies the following conditions, not just synchronized convexity.

- The zero coefficient array has price zero, and every tensor placed constantly at one point has price zero.
- For any map $\sigma:I\to J$ of finite slot types, the price of placing $T$ along $x\circ\sigma$ equals the price of placing the grouped tensor along $x:J\to X$. Grouping forms the product basis of the slots in each fiber of $\sigma$, with the same coefficients under that reindexing.
- The price of $D_{[2]}$ at two slots is their distance. For any $I$, the price of $D_I$ bounds each pairwise distance between the placed slots.
- The absolute difference of prices of $T$ under placements $x,y$ is at most $\sum_{i\in I}d(x_i,y_i)\log_2 |B_i|$, with the source's totalized real logarithm at zero.
- For each injective placement $x$ with $|I|\ge2$, one normalized spectral point $\phi$ works for **all** nonzero coefficient arrays $T$ on that slot type, of any finite local format: the price of $T$ is the price of $D_I$ times $\log_2\phi([T])$. Here $[T]$ is its class modulo mutual restriction by local linear maps, and $\phi$ is a semiring homomorphism to the nonnegative reals, monotone under the restriction preorder. Addition and multiplication of classes use direct sum and slotwise tensor product.

For a nonempty finite set of occupied sites, its diagonal price is obtained by placing the binary common diagonal with one slot at each distinct point. The empty set has diagonal price zero.

## CAT(0) comparison used for segments

For a metric space $X$, require that for each $x,y\in X$ there is a function $\gamma:\mathbb R\to X$ with $\gamma(0)=x$, $\gamma(1)=y$, and $d(\gamma(s),\gamma(t))=|s-t|d(x,y)$ for $s,t\in[0,1]$. Its values elsewhere are unconstrained. The CAT(0) comparison condition additionally requires, on the same segment, that for every $z\in X$ and every $t\in[0,1]$,

$$
d(z,\gamma(t))^2\le (1-t)d(z,x)^2+t d(z,y)^2-t(1-t)d(x,y)^2.
$$

The segment operation chooses one such function for each pair. Completeness or properness is not required. Synchronized convexity of a diagonal price along these segments is a separate hypothesis, not a consequence of the price structure alone.

## Expansion

Represent finite slot and local basis types with the coefficient reindexing for grouping. Build the restriction semiring and its normalized spectrum before expressing the representation field of the price. Keep the CAT(0) segment and its comparison inequality separate from the extra synchronized convexity condition.

## Sources

- OpenAI, [raw tensors and restriction](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/LinearAlgebra/SpectralBooks/SiteTensor/Raw.lean#L19-L46), [restriction semiring](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/LinearAlgebra/SpectralBooks/TensorSemiring.lean#L30-L91), and [normalized spectrum](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/LinearAlgebra/SpectralBooks/Spectrum.lean#L18-L23).
- OpenAI, [grouping and placement prices](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/LinearAlgebra/SpectralBooks/SpectralSpace.lean#L20-L63), [diagonal price](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/LinearAlgebra/SpectralBooks/SpectralDiagonal.lean#L18-L30), [metric segment and CAT(0) comparison](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Geometry/HyperbolicGroups/Basic.lean#L85-L98), and [chosen segment](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/OAI/Geometry/HyperbolicGroups/CATZero.lean#L13-L27).
