# Time-ordered product limit for near-identity matrices

Let $Y_M$ and $Y$ be functions from $[0, t]$ to the $d \times d$ real matrices, with $Y$ piecewise continuous and bounded, and suppose $Y_M \to Y$ uniformly on $[0, t]$ in operator norm. Then

$$\prod_{g < tM} \Bigl(I + \frac{1}{M}\, Y_M(g/M)\Bigr) \to \mathcal{T} \exp\Bigl(\int_0^t Y(s)\, ds\Bigr),$$

the time-ordered exponential of $Y$ on $[0, t]$: the value at time $t$ of the solution $\Phi$ of $\Phi' = \Phi Y$, $\Phi(0) = I$, with the factors of the product taken in the order of increasing $g$. For piecewise-constant $Y$ it is the product of the matrix exponentials of the pieces.

## Proof depends on

- [Global existence and uniqueness for globally Lipschitz ODEs](../../../Analysis/ordinary-differential-equations/maximal-solutions-and-global-existence/ode-global-exists-of-global-lipschitz.md)
- [The operator norm is submultiplicative](../../../Analysis/operator-theory/bounded-operators/operator-norm-submultiplicative.md)

## Expansion

1. Existence and uniqueness of $\Phi$, from [global existence for globally Lipschitz equations](../../../Analysis/ordinary-differential-equations/maximal-solutions-and-global-existence/ode-global-exists-of-global-lipschitz.md).
2. The convergence, by comparing one step of the product with $\Phi(s + 1/M)\Phi(s)^{-1}$ and summing the errors.
3. Checks: constant $Y$ gives $e^{tY}$, and $Y$ with two constant pieces gives the product of two exponentials.

## Sources

- R. C. Griffiths and S. Tavaré, Sampling theory for neutral alleles in a varying environment, *Philos. Trans. R. Soc. Lond. B* 344 (1994), 403–410, <https://pubmed.ncbi.nlm.nih.gov/7800710/> (motivation from variable population size).
