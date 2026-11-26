# Invariant coexistence iff the noise-corrected equilibrium is positive

**Model.** For $n$ species with densities $X_i(t)\ge0$, growth rates $\alpha\in\mathbb{R}^n$, interaction matrix $A\in\mathbb{R}^{n\times n}$, diffusion matrix $\Gamma\in\mathbb{R}^{n\times n}$ and an $n$-dimensional Brownian motion $B$,

$$dX_i=X_i\Big(\alpha_i+\sum_{j}A_{ij}X_j\Big)dt+X_i\sum_j\Gamma_{ij}\,dB_j .$$

**Assumption.** (a) $\Sigma=\Gamma\Gamma^\top$ is positive definite; (b) $A$ is Volterra-Lyapunov stable: $DA+A^\top D\prec0$ for some positive diagonal matrix $D$. Let $\beta=\alpha-\tfrac12\operatorname{diag}(\Sigma)$ be the noise-corrected (Ito-shifted) growth rates and $m=-A^{-1}\beta$, the interior equilibrium (possibly not positive) of the deterministic system $\dot x=\operatorname{Diag}(x)(\beta+Ax)$. For a face $J\subseteq[n]$ put $\widehat m^J=-(A^J)^{-1}\beta^J$ (principal submatrices are invertible under (b)) and let $m^J\in\mathbb{R}^n$ be its zero-padding. The invasion rate of species $i$ at a stationary law $\mu$ is $\lambda_i(\mu)=\int(\beta_i+(Ax)_i)\,\mu(dx)=\big(A(\mu(X)-m)\big)_i$, where $\mu(X)$ is the mean of $\mu$.

**Theorem.** Under the assumption, $X$ has an invariant probability measure $\pi$ with $\pi((0,\infty)^n)=1$ if and only if $m>0$. In that case $X$ is strongly stochastically persistent: $\pi$ is the unique invariant law on the interior, it is ergodic, its mean is $\int x\,\pi(dx)=m$, and $\|\mathbb{P}_x(X(t)\in\cdot)-\pi\|_{TV}\to0$ exponentially fast from every $x\in(0,\infty)^n$.

**Corollary (faces).** For each nonempty $J\subseteq[n]$, $X$ has an invariant law on the relative interior of the face $\mathbb{R}^J_+$ iff $\widehat m^J>0$; it is then unique, ergodic, with mean $m^J$. Every invariant law of $X$ is a convex combination of these face measures $\pi^J$ (with $\pi^\emptyset=\delta_0$).

## Expansion

Necessity: applying Ito's formula to $\log X_i$ and averaging under an ergodic law $\mu$ on the interior of face $J$ gives $\lambda_i(\mu)=0$ for $i\in J$, which forces $\mu(X)=m^J$ and $\widehat m^J>0$; with $J=[n]$ this gives $m>0$. Sufficiency: for every boundary ergodic law $\mu$ on face $J(\mu)$, the identity

$$m^\top\lambda(\mu)=-(m^{J(\mu)}-m)^\top A\,(m^{J(\mu)}-m)>0$$

holds because $A$ is negative definite after the diagonal rescaling. So the weights $p=m>0$ make $p^\top\lambda(\mu)$ positive uniformly over boundary laws, which is the Hening-Nguyen criterion for strong stochastic persistence. Stochastic coexistence is therefore decided exactly by the deterministic Lotka-Volterra system with growth rates lowered by half the noise variances, the stochastic analogue of the Volterra-Goh Lyapunov function argument.

## Sources

- Jorge Ramirez Osorio, "Coexistence and extinction in stochastic Lotka--Volterra systems with Volterra--Lyapunov stable interactions", arXiv:2610.28174 (2026), Theorem 2 and Corollary 2, with Proposition 1 and Lemma 3, <https://doi.org/10.48550/arXiv.2610.28174>
