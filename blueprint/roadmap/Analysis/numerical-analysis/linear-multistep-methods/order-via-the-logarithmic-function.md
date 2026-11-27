# Order of a linear multistep method from the function ρ(z)/log z − σ(z)

Let a [linear $k$-step method](linear-multistep-method.md) have first and second characteristic polynomials $\rho$ and $\sigma$, with $\rho(1) = 0$, $\rho'(1) = \sigma(1)$ and $\sigma(1) \ne 0$, and define, near $z = 1$, the function

$$\varphi(z) = \frac{\rho(z)}{\log z} - \sigma(z),$$

which has a removable singularity at $z = 1$. For a positive integer $p$, the method has [order of accuracy](order-of-accuracy-and-error-constants.md) $p$ if and only if $\varphi$ has a zero of multiplicity exactly $p$ at $z = 1$.

Applied to $y' = y$, $y(0) = 1$, on the mesh $x_n = nh$, the truncation error is $T_n = e^{nh}(\rho(e^h) - h\sigma(e^h))/(h\sigma(1))$, and $\rho(e^h) - h\sigma(e^h) = h\,\varphi(e^h)$; the equivalence compares the two expansions in powers of $h$.

## Depends on

- [Order of accuracy and error constants](order-of-accuracy-and-error-constants.md)
- [Linear multistep method](linear-multistep-method.md)

## Proof depends on

- [Order conditions](order-conditions.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 3.5, the function (75), Lemma 3 and its proof through (76). <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
