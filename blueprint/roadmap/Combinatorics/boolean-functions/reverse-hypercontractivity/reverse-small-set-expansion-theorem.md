# Reverse Small-Set Expansion Theorem

Let $A, B \subseteq \{-1,1\}^n$ have volumes $e^{-a^2/2}$ and $e^{-b^2/2}$ with $a, b \ge 0$, and let $0 \le \rho < 1$. Then a $\rho$-correlated pair $(x, y)$ satisfies

$$\Pr[x \in A,\ y \in B] \ge \exp\Big(-\frac{a^2 + 2\rho ab + b^2}{2(1 - \rho^2)}\Big).$$

So noise cannot make two sets of non-negligible volume nearly disjoint, which underlies results such as the impossibility of non-interactive correlation distillation.

## Proof sketch

If $\rho = 0$ the points are independent and the probability is $\mathrm{vol}(A)\mathrm{vol}(B)$, which is the bound. If $a = 0$ then $A$ is the whole cube and the probability is $\mathrm{vol}(B) = e^{-b^2/2} \ge e^{-b^2/(2(1-\rho^2))}$; likewise if $b = 0$. For $a, b > 0$ and $0 < \rho < 1$ apply two-function reverse hypercontractivity to $\mathbf{1}_A$ and $\mathbf{1}_B$ with $r = -\rho(\rho a + b)/(a + \rho b)$ and $s = -\rho(a + \rho b)/(\rho a + b)$ (O'Donnell, Ex. 10.9). Then $r, s < 0$ and $rs = \rho^2$, while $1 + r = a(1 - \rho^2)/(a + \rho b)$ and $1 + s = b(1 - \rho^2)/(\rho a + b)$ are both positive, so $\|\mathbf{1}_A\|_{1+r} = \mathrm{vol}(A)^{1/(1+r)}$ and $\|\mathbf{1}_B\|_{1+s} = \mathrm{vol}(B)^{1/(1+s)}$. The exponent of the resulting lower bound is $-\frac{a(a + \rho b) + b(b + \rho a)}{2(1 - \rho^2)}$, as claimed. (A negative exponent would not do: the quasinorm of the indicator of a proper subset is then $0$.)

## Depends on

- [Noise operator on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-noise-op.md)
- [Noise stability on the Boolean cube](../../../Analysis/harmonic-analysis/discrete-fourier-analysis/influences-and-the-noise-operator-on-the-boolean/bool-noise-stab.md)

## Proof depends on

- [Reverse hypercontractivity theorem on the cube](reverse-hypercontractivity-theorem.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
