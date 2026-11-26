# Reverse Small-Set Expansion Theorem

Let $A, B \subseteq \{-1,1\}^n$ have volumes $e^{-a^2/2}$ and $e^{-b^2/2}$ with $a, b \ge 0$, and let $0 \le \rho < 1$. Then a $\rho$-correlated pair $(x, y)$ satisfies

$$\Pr[x \in A,\ y \in B] \ge \exp\Big(-\frac{a^2 + 2\rho ab + b^2}{2(1 - \rho^2)}\Big).$$

So noise cannot make two sets of non-negligible volume nearly disjoint, which underlies results such as the impossibility of non-interactive correlation distillation.

## Proof sketch

Apply two-function reverse hypercontractivity to $\mathbf{1}_A$ and $\mathbf{1}_B$ with negative exponents $1 + r, 1 + s$ chosen in terms of $a, b, \rho$, using $\|\mathbf{1}_A\|_{1+r} = \mathrm{vol}(A)^{1/(1+r)}$, and optimize.

## Depends on

- [Noise operator on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-noise-op.md)
- [Noise stability on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-noise-stab.md)

## Proof depends on

- [Reverse hypercontractivity theorem on the cube](reverse-hypercontractivity-theorem.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
