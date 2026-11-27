# Kane-Nelson sparse Johnson-Lindenstrauss transform with O(eps^-1 log(1/delta)) nonzeros per column

For all $0 < \varepsilon, \delta < 1/2$ there is a probability distribution over real $m \times d$ matrices $\Pi$ with

$$
m = O(\varepsilon^{-2}\log(1/\delta)), \qquad s = O(\varepsilon^{-1}\log(1/\delta))
$$

nonzero entries in every column, each equal to $\pm 1/\sqrt{s}$, such that for every fixed $x \in \mathbb{R}^d$

$$
\Pr\big[\,\big|\|\Pi x\|_2^2 - \|x\|_2^2\big| > \varepsilon\|x\|_2^2\,\big] < \delta .
$$

Thus $\Pi x$ is computed in time $O(s\,\|x\|_0)$, where $\|x\|_0$ is the number of nonzero coordinates, and the number of rows is optimal by the Jayram–Woodruff bound. Two constructions work: each column chooses $s$ distinct rows at random, or the rows are split into $s$ blocks of size $m/s$ with one nonzero per block, with signs and positions drawn from $O(\log(1/\delta))$-wise independent hash families.

## Proof sketch

Write $\|\Pi x\|_2^2 - \|x\|_2^2 = \frac{1}{s}\sum_{r}\sum_{i \ne j} \eta_{r,i}\eta_{r,j}\sigma_{r,i}\sigma_{r,j}x_i x_j$, a quadratic form in the random signs $\sigma$ whose coefficients depend on the random positions $\eta$. Bound its $\ell = \Theta(\log(1/\delta))$-th moment: conditioned on positions, a Hanson–Wright or Khintchine-type moment inequality controls the form by the Frobenius and operator norms of its coefficient matrix, and a combinatorial count of position collisions bounds the moments of these norms. Markov's inequality on the $\ell$-th moment gives failure probability $\delta$.

## Proof depends on

- [Khintchine inequality](../../../../Probability/concentration-inequalities/khintchine-inequality.md)
- [Pairwise-independent hashing by affine maps over GF(2)](../../../../TheoryOfComputation/counting-complexity/counting-and-the-polynomial-hierarchy/pairwise-independent-hashing-by-affine-maps.md)

## Sources

- Daniel M. Kane, Jelani Nelson, "Sparser Johnson-Lindenstrauss Transforms", J. ACM 61 (2014), arXiv:1012.1577.
- Michael B. Cohen, T. S. Jayram, Jelani Nelson, "Simple Analyses of the Sparse Johnson-Lindenstrauss Transform", SOSA (2018).
- T. S. Jayram, David P. Woodruff, "Optimal Bounds for Johnson-Lindenstrauss Transforms and Streaming Problems with Sub-Constant Error", SODA (2011); ACM Trans. Algorithms (2013).
