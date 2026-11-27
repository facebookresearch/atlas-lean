# Finite free convolution preserves real-rootedness and obeys a root bound

If $p$ and $q$ are real-rooted then $p \boxplus_d q$ is real-rooted, and its largest root satisfies a finite analogue of Voiculescu's subordination bound: for every $\alpha > 0$,

$$
\mathrm{maxroot}\, \mathcal{U}_\alpha(p \boxplus_d q) \le \mathrm{maxroot}\, \mathcal{U}_\alpha p + \mathrm{maxroot}\, \mathcal{U}_\alpha q - \alpha d ,
$$

where $\mathcal{U}_\alpha p = p - \alpha p'$.

## Proof sketch

Real-rootedness follows from the identity $p \boxplus_d q = \hat q(\partial_x)\, p$, where $\hat q$ is the polynomial with $\hat q(\partial_x) x^d = q(x)$; for real-rooted $q$ the operator $\hat q(\partial_x)$ preserves real-rootedness of degree-$d$ polynomials by the Laguerre-Pólya-Schur theory. The root bound uses the barrier function method: track the inverse of the Cauchy transform $G_p(x) = p'(x)/p(x)$ and show that inverse Cauchy transforms are subadditive up to the stated correction.

## Depends on

- [Finite free additive convolution of polynomials](finite-free-additive-convolution.md)

## Proof depends on

- [Mixed characteristic polynomial](../../../Analysis/operator-algebras/kadison-singer-problem/mixed-characteristic-polynomial.md)

## Sources

- Adam W. Marcus, Daniel A. Spielman, Nikhil Srivastava, "Finite free convolutions of polynomials", Probability Theory and Related Fields 182 (2022); arXiv:1504.00350.
