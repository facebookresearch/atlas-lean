# Absolute stability of a linear multistep method

Apply a [linear $k$-step method](../linear-multistep-method.md) with characteristic polynomials $\rho$ and $\sigma$ to the model problem $y' = \lambda y$, $\lambda \in \mathbb{C}$, with step $h > 0$. With $\bar h = h\lambda$ it becomes the linear recurrence $\sum_{j=0}^{k} (\alpha_j - \bar h \beta_j) y_{n+j} = 0$, whose *stability polynomial* is

$$\pi(z; \bar h) = \rho(z) - \bar h\, \sigma(z).$$

The method is *absolutely stable* for a given $\bar h \in \mathbb{C}$ if $\alpha_k - \bar h \beta_k \ne 0$, so that $\pi(\cdot\,; \bar h)$ has degree $k$ and the recurrence determines $y_{n+k}$, and every root $r$ of $\pi(\cdot\,; \bar h)$ satisfies $|r| < 1$, and *absolutely unstable* for $\bar h$ otherwise. Its *region of absolute stability* is the set $R_A$ of all $\bar h \in \mathbb{C}$ for which it is absolutely stable, and an interval $(\alpha, \beta)$ of real numbers on which it is absolutely stable is an *interval of absolute stability*. For example, Euler's explicit method has $\pi(z; \bar h) = z - (1 + \bar h)$ and $R_A = \{\bar h : |1 + \bar h| < 1\}$.

## Depends on

- [Linear multistep method](../linear-multistep-method.md)

## Sources

- E. Süli, *Numerical Solution of Ordinary Differential Equations*, lecture notes, Mathematical Institute, University of Oxford, version of 2 March 2022, Section 3.6, the stability polynomial (78) and Definition 9, Section 4, Definition 10 and Exercise 6(a). <https://people.maths.ox.ac.uk/suli/nsodes.pdf>
