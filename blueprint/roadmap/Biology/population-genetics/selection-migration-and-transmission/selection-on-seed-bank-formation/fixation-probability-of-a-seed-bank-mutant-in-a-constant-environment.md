# Fixation probability of a seed-bank mutant in a constant environment

**Setting.** The Wright–Fisher seed-bank model with germination-delay distribution $\mathbf b=(b_0,\dots,b_K)$, $b_0>0$, mean delay $B=\sum_i ib_i$, and population size $N$. Let $\mathbf x^N(t)$ be the vector of mutant frequencies among mature plants of the last $K+1$ generations, with time measured in units of $N$ generations.

**Diffusion limit (Theorem 2.3).** If $\mathbf x^N(0)\to\mathbf x(0)$ on the diagonal $\Gamma=\{x_0=\dots=x_K\}$, then $\mathbf x^N$ converges in distribution to a diffusion that stays on $\Gamma$, whose common coordinate satisfies

$$dx_0=\tfrac12\,x_0(1-x_0)\,\partial^2_{x_0}\Phi_0(\mathbf x)\,dt+\frac{\sqrt{x_0(1-x_0)}}{B(1-x_0)+1}\,dW_0 ,$$

where $\Phi$ is the projection along the deterministic flow onto $\Gamma$ and $W_0$ is a Brownian motion. The drift is positive, and the noise is damped by the factor $1/(B(1-x_0)+1)$.

**Fixation bound (Theorem 2.5).** Let $T_a=\inf\{t:x_0(t)=a\}$ and

$$\Psi(B,y)=1-e^{-B\psi_B(y)}+\psi_B(y)\,e^{-B\psi_B(y)},\qquad \psi_B(y)=\frac{1}{2(B+1)^2}\log\frac{B+1}{B+e^{-2y}} .$$

For $y\in(0,1)$, $B\mapsto\Psi(B,y)$ is strictly decreasing, with $\Psi(B,y)\to y$ as $B\to0$ and $\Psi(B,y)\to0$ as $B\to\infty$; and for every $K$ and admissible $\mathbf b$,

$$\mathbb P\big(T_1<T_0\ \big|\ x_0(0)=\psi_B(y)\big)\le\Psi(B,y).$$

Since a neutral allele without seed bank started at frequency $y$ fixes with probability $y$, a mutation conferring a seed bank fixes less often than a neutral one in a constant environment.

## Depends on

- [Critical branching phase of a seed-bank mutant](critical-branching-phase-of-a-seed-bank-mutant.md)

## Proof idea

The deterministic part of the dynamics is a strong drift that collapses the frequency vector onto $\Gamma$ in $O(1)$ generations; Katzenberger's theorem for SDEs forced onto a manifold gives the limit on $\Gamma$, with an induced drift from the curvature of $\Phi$. The positive drift does not compensate for the smaller frequency $\psi_B(y)<y$ that the seed-bank family reaches by the end of the branching phase; bounding the scale function of the limiting diffusion yields $\Psi$. In slowly or rapidly fluctuating environments the paper derives modified limits in which seed banks can be favoured.

## Sources

- A. Etheridge and J. L. de Oliveira Madeira, "How seed banks evolve in plants: a stochastic dynamical system subject to a strong drift", Electronic Journal of Probability 31 (2026), 1–82, <https://doi.org/10.1214/26-EJP1596>. Numbering as in the preprint arXiv:2602.04437v1, <https://arxiv.org/abs/2602.04437v1>: Section 2.1, Lemma 2.2, Theorems 2.3 and 2.5, Section 3.
