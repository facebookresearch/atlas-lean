# Large deviation principle for piecewise-deterministic reaction networks

**Model.** A reaction network has $d$ species and a finite set $\mathscr R$ of reactions with reaction vectors $\xi_\alpha\in\mathbb Z^d$. For system size $N$, the scaled concentration and the scaled reaction counts satisfy

$$x(t)=N^{-1}X(0)+\sum_{\alpha\in\mathscr R}z_\alpha(t)\,\xi_\alpha ,$$

where reaction $\alpha$ fires with intensity $N\lambda_\alpha\big(x(t),u(t)\big)$, $\lambda_\alpha$ continuous, bounded, and zero whenever firing would make a concentration negative. The continuous variables $u\in\mathbb R^m$ (for instance cytosolic calcium) follow an ODE $\dot u=A(u,x)$ driven by $x$, with $A$ continuous, so $(z,x,u)$ is a piecewise-deterministic Markov process (PDMP). Assume, as the source does for Theorem 1.1:

- non-random initial conditions $u(0)=\hat u^N_0$ and $x(0)=\hat x^N_0$ with $z(0)=0$, and limits $\hat u^N_0\to\hat u_0$ and $\hat x^N_0\to\hat x_0$ as $N\to\infty$ ((10)–(12));
- growth bounds: for a constant $K>0$, all $u$, $x$ and all $\alpha\in\mathscr R$, $\lVert A(u,x)\rVert\le K(1+\lVert u\rVert+\lVert x\rVert)$ and $\lambda_\alpha(x,u)\le K$ ((13)–(14));
- uniform Lipschitz bounds: for a constant $C$, $\lVert A(u,x)-A(\tilde u,\tilde x)\rVert\le C(\lVert u-\tilde u\rVert+\lVert x-\tilde x\rVert)$ and $\sup_{\alpha}\lvert\lambda_\alpha(x,u)-\lambda_\alpha(\tilde x,\tilde u)\rvert\le C(\lVert u-\tilde u\rVert+\lVert x-\tilde x\rVert)$ ((15)–(16)).

**Theorem (large deviation principle).** Let $\mathcal O$ be open and $\mathcal A$ closed in the path space of $(z,x,u)$, and suppose the reaction rates stay bounded away from zero on $\mathcal A\cup\mathcal O$ over every finite time window. Then

$$\limsup_{N\to\infty}N^{-1}\log\mathbb P\big((z,x,u)\in\mathcal A\big)\le-\inf_{\mathcal A}\mathcal J,\qquad \liminf_{N\to\infty}N^{-1}\log\mathbb P\big((z,x,u)\in\mathcal O\big)\ge-\inf_{\mathcal O}\mathcal J,$$

with the lower semicontinuous rate function with compact level sets

$$\mathcal J(z,x,u)=\sum_{\alpha\in\mathscr R}\int_0^\infty \ell\!\Big(\frac{\dot z_\alpha(r)}{\lambda_\alpha(x(r),u(r))}\Big)\lambda_\alpha(x(r),u(r))\,dr,\qquad \ell(a)=a\log a-a+1,$$

for absolutely continuous $z$ (and $\mathcal J=\infty$ otherwise, or if some $z_\alpha$ increases on a set of positive measure where $\lambda_\alpha=0$).

**Two-state channels.** For $N$ channels switching open$\to$closed at rate $\lambda_1(x,u)$ and closed$\to$open at rate $\lambda_2(x,u)$ (reaction 1 is $1\to0$, reaction 2 is $0\to1$), with $x$ the open fraction, the reduced Lagrangian in terms of $(\dot x,x,u)$ is

$$\hat L(\dot x,x,u)=\ell\Big(\frac{\dot z_1}{\lambda_1}\Big)\lambda_1+\ell\Big(\frac{\dot x+\dot z_1}{\lambda_2}\Big)\lambda_2,\qquad \dot z_1(\dot x+\dot z_1)=\lambda_1\lambda_2,$$

taking the root $\dot z_1\ge0$; it is convex in $\dot x$, and optimal first-hitting trajectories solve the corresponding Euler–Lagrange equations.

## Expansion

Write each reaction counter as a time-changed unit Poisson process; the empirical paths of the rescaled Poisson processes satisfy a Sanov-type LDP with rate $\sum_\alpha\int\ell(\dot y_\alpha)$. The map from these driving paths to $(z,x,u)$, solving the random time change together with the ODE for $u$, is continuous and one-to-one on sets where all rates are at least $\epsilon>0$, so the contraction principle transfers the LDP; exponential tightness handles the noncompact path space. Minimizing $\hat L$ over paths that reach a high-calcium state estimates the exponentially small probability that microscopic channel noise triggers a cell-wide calcium wave.

## Sources

- Gaetan Barbet, James MacLaurin, Moshe Silverstein, "Large Deviations of Piecewise-Deterministic-Markov-Processes with Application to Stochastic Calcium Waves", arXiv:2406.12493: Section 1 (model), Theorem 1.1 and the rate function of Section 1.1, Lemma 1.2 (path space), Lemma 2.1 (convexity), Lemmas 3.1–3.3 (two-state channel Lagrangian), Theorem 4.1 (Sanov-type LDP), Lemmas 4.2–4.4 (contraction and exponential tightness). <https://doi.org/10.48550/arXiv.2406.12493> Published version: G. Barbet, J. MacLaurin, M. Silverstein, P. Vilanova, "Large deviations of piecewise-deterministic Markov processes with application to stochastic calcium waves", Journal of Mathematical Biology 93 (2026) 41, <https://doi.org/10.1007/s00285-026-02446-7>.
