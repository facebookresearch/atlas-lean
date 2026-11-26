# Planar Laughlin gap on homogeneous occupation blocks

For fixed $N\geq0$, an input is a sequence of vectors $\psi_L$ ($L\geq0$) in exterior algebras on orbitals $0,\ldots,L$, written in increasing occupation order. At block $L$, coefficients vanish unless the subset has size $N$ and its orbitals sum to $L$. Let $P_{L,p}=\sum_{i,j=0}^{L} c_{pij}a_ja_i$, with signed exterior annihilation $a_i$ and real $c_{pij}=0$ unless $i+j=p+1$, in which case $c_{pij}=\tfrac12(i-j)\sqrt{p!/(2^p i!j!)}$. Put $H_L=\sum_{p=0}^{2L}P_{L,p}^*P_{L,p}$. With extended nonnegative sums, the bound is

$$
\frac{4616733319001}{10^{14}}\sum_{L\geq0}\sum_{p=0}^{2L}\|P_{L,p}\psi_L\|^2\leq \sum_{L\geq0}\|H_L\psi_L\|^2.
$$

There is no assumed global square summability and the constant is the endpoint itself.

## Depends on
The signed exterior occupation basis, the planar limiting coefficients with the factor $1/2$, and extended nonnegative sums over homogeneous blocks.

## Proof depends on
The finite-block limit from the spherical coefficient matrices and a uniform bound that permits increasing the gap parameter to its endpoint.

## Expansion
Identify the fixed-occupation block and control convergence of every matrix entry; then pass positivity to each finite block, let $\gamma$ increase, and sum the resulting inequalities in the extended nonnegative reals.

## Sources

- OpenAI, [comparator statement](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/LaughlinPlanar.lean#L75-L79) and [formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/269.md).
