# Some quadratic Julia sets with a computable parameter are not computable

There are computable complex parameters $c$ for which the Julia set of $z^2 + c$ cannot be drawn to arbitrary precision by any algorithm, even one with access to $c$.

A compact set $K \subset \mathbb{R}^k$ is *computable* if there is a Turing machine that, on input $m$, outputs (an encoding of) a finite union $C_m$ of closed balls with dyadic rational centers and radii such that the Hausdorff distance satisfies $d_H(K, C_m) < 2^{-m}$. For a parameter $c$ given by an oracle (a function $\phi$ returning dyadic approximations of $c$ with $|\phi(n) - c| < 2^{-n}$), $J_c$ is computable *with an oracle for $c$* if a single oracle Turing machine does the same when given any such oracle. For $c \in \mathbb{C}$ let $J_c$ be the Julia set of $z \mapsto z^2 + c$, a compact subset of $\mathbb{C} = \mathbb{R}^2$. A real or complex number is computable if a Turing machine outputs approximations of it to within $2^{-n}$ on input $n$.

**Theorem.** There exist computable values of the parameter $c$ such that the Julia set $J_c$ is not computable by a Turing machine with an oracle access to $c$ (Corollary 6.7 of the source). Since such $c$ is computable, $J_c$ is in particular not a computable compact set.

The parameters are Siegel parameters: $c = \lambda/2 - \lambda^2/4$ with $\lambda = e^{2\pi i \theta}$, for which $z^2 + c$ is conjugate to $P_\theta(z) = z^2 + e^{2\pi i\theta} z$, whose fixed point $0$ lies in a Siegel disk when $\theta$ is a Brjuno number.

## Depends on

- [Julia set of a quadratic polynomial z² + c](../julia-sets-of-positive-area/julia-set.md)

## Proof depends on

- [The halting problem for single-tape machines is undecidable](../../../TheoryOfComputation/computability/halting-problem-for-single-tape-turing-machines/exists-not-tm2-decidable-tm0-halts-on.md)

## Expansion

Let $r(\theta)$ be the conformal radius of the Siegel disk $\Delta_\theta$ of $P_\theta$ (and $r(\theta) = 0$ when $\theta$ is not a Brjuno number), and $r_{\sup} = \sup_\theta r(\theta)$. The source shows that $J_\theta$ is computable by a machine with an oracle for $\theta$ if and only if $r(\theta)$ is (Theorem 6.4), and characterizes the conformal radii at computable rotation numbers: a real $r \in (0, r_{\sup})$ equals $r(\theta)$ for some computable $\theta$ if and only if $r$ is right-computable, that is, the limit of a computable nonincreasing sequence of rationals (Theorem 6.6). Right-computable numbers that are not computable are dense in $\mathbb{R}$ (Proposition 2.2); taking such an $r_*$ gives a computable $\theta_*$ with $r(\theta_*) = r_*$ not computable even with an oracle for $\theta_*$, so $J_{\theta_*}$, and $J_c$ for the corresponding computable $c$, is not computable. By contrast, the filled Julia set of every polynomial is computable from its coefficients (Theorem 5.1), and $J_\theta$ is computable with an oracle for $\theta$ when $\theta$ has bounded type (Proposition 6.5). The result first appeared in the authors' paper on non-computable Julia sets.

## Sources

- M. Braverman and M. Yampolsky, "Computability of Julia sets", Moscow Mathematical Journal 8 (2008), no. 2, 185–231, https://doi.org/10.17323/1609-4514-2008-8-2-185-231; read in arXiv:math/0610340v2 (Definition 2.5, Proposition 2.2, Theorem 5.1, Theorems 6.4 and 6.6, Proposition 6.5 and Corollary 6.7 of arXiv:math/0610340v2).
- M. Braverman and M. Yampolsky, "Non-computable Julia sets", Journal of the American Mathematical Society 19 (2006), no. 3, 551–578, https://doi.org/10.1090/S0894-0347-05-00516-3; cited for attribution of the first proof.
