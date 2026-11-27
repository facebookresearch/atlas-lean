# Coherent risk measures

Let $\mathcal{H}$ be a linear space of real functions on a set $\Omega$. A functional $\rho$ on real functions on $\Omega$ is a coherent risk measure on $\mathcal{H}$ if $\mathcal{H}$ contains the constants and: $\rho(X) \le \rho(Y)$ whenever $Y \le X$ in $\mathcal{H}$; $\rho(1) = -1$ and $\rho(-1) = 1$; $\rho(X + Y) \le \rho(X) + \rho(Y)$ for $X, Y \in \mathcal{H}$; and $\rho(cX) = c \, \rho(X)$ for $X \in \mathcal{H}$ and $c \ge 0$.

## Idea

Here $X$ is the future value of a financial position and $\rho(X)$ is the amount of capital that must be added to make it acceptable. Monotonicity says that a position that is always worth more needs less capital; subadditivity says that merging two positions does not create risk, so diversification is rewarded; positive homogeneity says that risk scales with the size of the position. Together with the normalisation these give $\rho(c) = -c$ for constants and the cash invariance $\rho(X + c) = \rho(X) - c$. Coherent risk measures are sublinear expectations of the loss: $\rho(X) = \mathbb{E}[-X]$ for a sublinear expectation $\mathbb{E}$, and conversely. The positions with $\rho(X) \le 0$ form a coherent acceptable set. Value at risk is the standard example of a risk measure that is not coherent, since it can fail subadditivity.

## Statements

- [Coherent risk measure](is-coherent-risk-measure.md)
- [Coherent risk measures of constants](map-const.md): basic property: values on constants
- [Sublinear expectations give coherent risk measures](is-coherent-risk-measure-2.md): sublinear expectations give coherent risk measures
- [Coherent risk measures give sublinear expectations](is-sublinear-expectation-2.md): converse direction
- [Coherent acceptable set](is-coherent-acceptable-set.md): definition of the acceptance sets that correspond to coherent risk measures
- [The acceptance set of a coherent risk measure](is-coherent-acceptable-set-2.md): basic property: the acceptance set is coherent

## Background

- [Sublinear expectations and their representation](../sublinear-expectations/README.md)

## Sources

- P. Artzner, F. Delbaen, J.-M. Eber and D. Heath, *Coherent measures of risk*, Mathematical Finance (1999).
- S. Peng, *Nonlinear Expectations and Stochastic Calculus under Uncertainty*, arXiv:1002.4546, 2010.
