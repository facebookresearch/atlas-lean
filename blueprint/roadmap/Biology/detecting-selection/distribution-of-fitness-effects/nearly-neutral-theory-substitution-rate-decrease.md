# Monotonicity of the deleterious F-based rate model

Fix $u>0$ and a probability measure $\mu$ on $(-\infty,0]$, independent
of $N$. With the [scaling function](../../molecular-evolution/substitution-rate-with-selection.md)
$F(0)=1$ and $F(-y)=y/(e^y-1)$ for $y>0$, **define**

$$\frac{k_N}u=\int F(4Ns)\,\mu(ds),\qquad N>0.$$

This is the F-based rate model, not an assertion of a uniform finite
Wright–Fisher approximation over $\mu$.
The function $N\mapsto k_N$ is nonincreasing. It is strictly decreasing
between any two distinct positive $N$ precisely when
$\mu(( -\infty,0))>0$. Also $k_N/u\to\mu(\{0\})$ as $N\to\infty$.
For $u=0$ the unnormalized rate is identically zero, so strict decrease
of $k_N$ is not asserted.

## Depends on

- [Selected scaling function and finite-size distinction](../../molecular-evolution/substitution-rate-with-selection.md)

## Expansion

$F$ is strictly increasing. For every $s<0$, $4Ns$ strictly decreases
with $N$; at $s=0$ the integrand stays one. Integrating the strict
positive difference proves the stated criterion for strictness.
On the support, $0<F(4Ns)\le1$, and it tends to zero at every negative
$s$. Dominated convergence leaves just the neutral atom.
Beneficial mass invalidates a universal monotonicity claim: for
$\mu=\delta_{s_0}$ with $s_0>0$, this same rate model increases with $N$.
A neutral-plus-deleterious mixture approaches its neutral fraction times
$u$; no atom at a literal infinite negative selection coefficient is needed.

## Sources

- T. Ohta, "Slightly deleterious mutant substitutions in evolution", Nature 246 (1973), 96–98, <https://doi.org/10.1038/246096a0>. The monotonicity is derived above.
