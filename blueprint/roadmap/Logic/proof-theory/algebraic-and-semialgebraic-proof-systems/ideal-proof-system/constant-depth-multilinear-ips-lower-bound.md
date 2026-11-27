# Constant-depth multilinear IPS lower bound for lifted knapsack

Over characteristic zero, every multilinear polynomial that agrees with the inverse of the lifted knapsack polynomial $\sum_{i,j,k,\ell} z_{ijk\ell} x_i x_j x_k x_\ell - \beta$ on the Boolean cube needs product-depth-$\Delta$ circuits of size $n^{\Omega((\log n)^{2^{1-2\Delta}}/\Delta)}$, a super-polynomial lower bound for constant-depth multilinear IPS refutations.

**Theorem.** Let $n$ and $\Delta$ be positive integers and $\mathrm{char}(\mathbb{F}) = 0$. Let $g$ be a polynomial of individual degree at most $\delta = 1$ that agrees with

$$
\frac{1}{\sum_{i,j,k,\ell \in [n]} z_{ijk\ell} \, x_i x_j x_k x_\ell - \beta}
$$

on all Boolean values of the variables. Then every circuit of product-depth at most $\Delta$ computing $g$ has size at least

$$
n^{\Omega\left( \frac{(\log n)^{2^{1 - 2\Delta}}}{\Delta} \right)} .
$$

By the functional lower bound method this gives the same lower bound, over the same field, for multilinear constant-depth IPS refutations of $\sum_{i,j,k,\ell} z_{ijk\ell} x_i x_j x_k x_\ell - \beta$ together with the Boolean axioms.

## Proof sketch

This improves the exponent of the multilinear lower bound of Govindasamy, Hakoniemi and Tzameret for the same instance from $1/(2^{2\Delta} - 1)$ to $1/2^{2\Delta - 1}$. A partial assignment maps the instance to a knapsack polynomial over a balanced word of degree at most $4$; the circuit is expanded to a formula of size $s^{O(\Delta)}$, homogenization gives a homogeneous formula of product-depth $2\Delta$ for a degree slice, and a lower bound for the affine-projections-of-partials measure, in the framework of Amireddy, Garg, Kayal, Saha and Thankey adapted to functional lower bounds, finishes the argument with $d = \lfloor \log n \rfloor$. The instance has a small constant-depth refutation of individual degree $O(n^3)$, obtained by substituting the gadget into the depth-3 refutations of plain knapsack. The cited version states the theorem for every individual degree $\delta$, with $\delta^2$ entering the denominator of the exponent; this page records the case $\delta = 1$.

## Depends on

- [Linear and circuit-restricted Ideal Proof Systems](linear-and-restricted-ideal-proof-systems.md)

## Proof depends on

- [Functional lower bound method for linear IPS](functional-lower-bound-method.md)

## Sources

- Tuomas Hakoniemi, Nutan Limaye, Iddo Tzameret, "Functional lower bounds in algebraic proofs: symmetry, lifting, and barriers", *56th ACM Symposium on Theory of Computing (STOC 2024)*, 2024, https://doi.org/10.1145/3618260.3649616; numbering of arXiv:2412.20114v1 (Theorem 44 with $\delta = 1$, Lemma 59, Section 6).
