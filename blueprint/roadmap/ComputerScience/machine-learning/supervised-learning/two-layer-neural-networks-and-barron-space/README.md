# Two-layer neural networks and Barron space

Two-layer ReLU networks $f(x) = \sum_k a_k \max(\langle w_k, x \rangle, 0)$, measured by the path
norm $\sum_k \lvert a_k \rvert \lVert w_k \rVert_1$ rather than by their width, in the approach of
W. E, C. Ma and L. Wu: the Barron space is the function space naturally attached to these
networks, on which approximation and estimation errors scale like Monte Carlo rates, $m^{-1/2}$
in the width and $n^{-1/2}$ in the sample size, independently of the input dimension $d$. The
empirical Rademacher complexity of a path-norm ball is at most $2 Q \sqrt{2 \log(2d) / n}$, by
the Rademacher calculus (homogeneity, contraction and Massart's lemma), with and without a bias
term; with a bias the proof gives $\log(2(d+1))$. The direct approximation theorem, approximation
of every Barron function by width-$m$ networks with squared error $3 \lVert f \rVert_B^2 / m$ and
path norm $2 \lVert f \rVert_B$, follows by Monte Carlo sampling of the neurons; the inverse
approximation theorem, which together with it identifies the Barron space with the functions
approximable by networks of bounded path norm, and the a priori estimate of the population risk
of the path-norm regularized estimator, which combines approximation and estimation into a
width-independent $O(n^{-1/2})$ bound, complete the picture.

## Barron space

- [The unit cube](unit-cube.md)
- [ReLU neuron](relu-neuron.md)
- [Barron representation](is-barron-representation.md)
- [Barron norm](barron-norm.md)
- [A single neuron lies in the Barron space](barron-norm-neuron-le.md)
- [Direct approximation theorem for the Barron space](barron-direct-approximation.md)
- [Inverse approximation theorem for the Barron space](barron-inverse-approximation.md)

## Path-norm balls and their Rademacher complexity

- [Two-layer ReLU network](two-layer-re-lu.md)
- [Path norm](path-norm.md)
- [Path-norm ball on a sample](path-norm-ball-values.md)
- [Rademacher complexity of path-norm balls of two-layer ReLU networks](rademacher-complexity-path-norm-ball-val.md)
- [Two-layer ReLU network with bias](two-layer-re-lubias.md)
- [Path norm with bias](path-norm-bias.md)
- [Path-norm ball with bias on a sample](path-norm-ball-bias-values.md)
- [Rademacher complexity of path-norm balls of two-layer ReLU networks with bias](rademacher-complexity-path-norm-ball-bia.md)

## Generalization

- [A priori estimate of the population risk for two-layer ReLU networks](two-layer-a-priori-estimate.md)

## Supporting definitions and lemmas

- [Step 1: homogeneity](sup-corr-path-norm-ball-values-le.md)
- [Step 2: contraction](rademacher-complexity-l1-neuron-values-l.md)
- [Step 3: the $\ell^1$ ball](rademacher-complexity-l1-linear-values-l.md)
- [Step 4: Massart](rademacher-complexity-signed-columns-le.md)
- [Correlation of one neuron](abs-sign-corr-neuron-le.md)
- [Linear functionals on the $\ell^1$ unit ball](l1-linear-values.md)
- [ReLU neurons on the $\ell^1$ unit ball](l1-neuron-values.md)
- [Signed coordinate functionals](signed-columns.md)
- [Bias as an extra input coordinate](path-norm-ball-bias-values-eq.md)

## Related topics

- [Rademacher complexity](../../generalization-bounds-and-concentration/rademacher-complexity/README.md): the calculus (scaling, contraction, Massart's finite-class lemma) from which the bound for path-norm balls is assembled, and the risk bound that turns it into a generalization guarantee.
- [Generalization bounds and concentration](../../generalization-bounds-and-concentration/README.md): the dimension-free bound for balls of linear predictors in a Hilbert space, the $\ell^2$ counterpart of the $\ell^1$ geometry of the path norm.
- [Universal approximation theorem](../../../../Analysis/approximation-theory/universal-approximation.md): the qualitative density of two-layer networks, which gives no rate; the Barron space is where a dimension-free rate holds.
- [Positive-definite kernels](../../../../Analysis/hilbert-spaces/positive-definite-kernels/README.md): random-feature and kernel models fix the inner weights; E, Ma and Wu describe the Barron space as the union of the reproducing kernel Hilbert spaces of the kernels $k_\pi(x, x') = \mathbb{E}_{(b, c) \sim \pi} \sigma(\langle b, x \rangle + c) \sigma(\langle b, x' \rangle + c)$, with the bias $c$ of the Barron representations and $\pi$ a probability measure on the $\ell^1$ unit sphere $\lVert b \rVert_1 + \lvert c \rvert = 1$ of the augmented inner
weights $(b, c) \in \mathbb{R}^{d+1}$.
- [Backpropagation](../backpropagation/README.md): the gradient computation used to train these networks.
