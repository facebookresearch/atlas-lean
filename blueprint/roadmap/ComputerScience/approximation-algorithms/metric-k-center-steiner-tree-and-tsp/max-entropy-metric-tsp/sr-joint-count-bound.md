# Joint count probabilities for strongly Rayleigh measures (Karlin-Klein-Oveis Gharan)

Let $\mu$ be strongly Rayleigh on $2^{[m]}$, let $A_1,\dots,A_n$ count elements in disjoint subsets of $[m]$, and fix $\kappa \in \mathbb{Z}_{\ge 0}^{n}$. Suppose that for all $I \subseteq [n]$

$$
\mathbb{P}_\mu[A_I \ge \kappa_I] \ge \epsilon \quad\text{and}\quad \mathbb{P}_\mu[A_I \le \kappa_I] \ge \epsilon .
$$

Then

$$
\mathbb{P}_\mu[A_1=\kappa_1,\dots,A_n=\kappa_n] \ge f(\epsilon)\,\mathbb{P}_\mu[A_{[n]}=\kappa_{[n]}], \qquad f(\epsilon) \ge \epsilon^{2^{n}}\prod_{i=2}^{n}\frac{1}{\max\{\kappa_i,\kappa_{[i-1]}\}+1}.
$$

In the exact case $\kappa=\mathbf{1}$ and $\mathbb{E}[A_i]=1$ for all $i$, Gurvits' capacity inequality gives $\mathbb{P}[A_1=\dots=A_n=1] \ge e^{-n}$.

## Proof sketch

Project $\mu$ onto the sets and symmetrize to a strongly Rayleigh measure on $n$ blocks; then induct on $n$, splitting off one block at a time and using that the conditional law of a block count given $A_{[i-1]}$ remains strongly Rayleigh and Poisson-binomial. Each step loses a factor polynomial in $\epsilon$ and in the largest count, which compounds doubly exponentially. The exact case follows from Gurvits' inequality $\partial_{z_1}\cdots\partial_{z_n}p|_{z=0} \ge e^{-n}\inf_{z > 0}p(z)/(z_1\cdots z_n)$ for real stable $p$ with nonnegative coefficients.

## Depends on

- [Strongly Rayleigh probability measures on subsets of a ground set](strongly-rayleigh-measure.md)

## Proof depends on

- [Negative dependence and Poisson-binomial counts under strongly Rayleigh measures](strongly-rayleigh-negative-dependence.md)
- [Real stable polynomials](../../../../Algebra/zeros-of-polynomials/stable-polynomials/is-real-stable.md)

## Sources

- Anna R. Karlin, Nathan Klein, Shayan Oveis Gharan, "A (Slightly) Improved Approximation Algorithm for Metric TSP", STOC (2021), arXiv:2007.01409.
- Leonid Gurvits, "Hyperbolic Polynomials Approach to Van der Waerden/Schrijver-Valiant Like Conjectures: Sharper Bounds, Simpler Proofs and Algorithmic Applications", STOC (2006).
