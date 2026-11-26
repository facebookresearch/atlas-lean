# Extinction rates on the saturated face

**Model.** For $n$ species with densities $X_i(t)\ge0$, growth rates $\alpha\in\mathbb{R}^n$, interaction matrix $A\in\mathbb{R}^{n\times n}$, diffusion matrix $\Gamma\in\mathbb{R}^{n\times n}$ and an $n$-dimensional Brownian motion $B$,
$$dX_i=X_i\Big(\alpha_i+\sum_{j}A_{ij}X_j\Big)dt+X_i\sum_j\Gamma_{ij}\,dB_j .$$
**Assumption.** (a) $\Sigma=\Gamma\Gamma^\top$ is positive definite; (b) $A$ is Volterra-Lyapunov stable: $DA+A^\top D\prec0$ for some positive diagonal matrix $D$. Let $\beta=\alpha-\tfrac12\operatorname{diag}(\Sigma)$ be the noise-corrected (Ito-shifted) growth rates and $m=-A^{-1}\beta$, the interior equilibrium (possibly not positive) of the deterministic system $\dot x=\operatorname{Diag}(x)(\beta+Ax)$. For a face $J\subseteq[n]$ put $\widehat m^J=-(A^J)^{-1}\beta^J$ (principal submatrices are invertible under (b)) and let $m^J\in\mathbb{R}^n$ be its zero-padding. The invasion rate of species $i$ at a stationary law $\mu$ is $\lambda_i(\mu)=\int(\beta_i+(Ax)_i)\,\mu(dx)=\big(A(\mu(X)-m)\big)_i$, where $\mu(X)$ is the mean of $\mu$.

Under (b) the deterministic system $\dot x=\operatorname{Diag}(x)(\beta+Ax)$ has a unique *saturated* nonnegative equilibrium $\bar x$ (one with $(\beta+A\bar x)_i\le0$ wherever $\bar x_i=0$). If $m>0$ fails, $\bar x$ lies in the relative interior of a proper face $\mathbb{R}^S_+$, $S\subsetneq[n]$, called the saturated face.

**Theorem.** Assume (a)-(b) and that $m>0$ fails. For every $X(0)\in(0,\infty)^n$, almost surely the occupation measures $\frac1t\int_0^t\delta_{X(s)}ds$ converge weakly to the face measure $\pi^S$, and
$$\lim_{t\to\infty}\frac1t\int_0^tX(s)\,ds=m^S,\qquad \lim_{t\to\infty}\frac{\log X_i(t)}{t}=\lambda_i(\pi^S)=(\beta+Am^S)_i\le0\quad(i\in[n]).$$
In particular every species $i\notin S$ with $(\beta+Am^S)_i<0$ goes extinct exponentially fast at that rate, and the survivors settle in the stationary regime $\pi^S$ with mean $m^S=\bar x$.

## Depends on

- [Invariant coexistence iff the noise-corrected equilibrium is positive](invariant-coexistence-iff-positive-noise-corrected-equilibrium.md)

## Expansion

An invariant law that no absent species can invade ($\lambda(\mu)\le0$) must be a face measure $\pi^J$ with mean $m^J=\bar x$, so it is $\pi^S$; uniqueness of the saturated equilibrium under Volterra-Lyapunov stability makes this law unique. The general Hening-Nguyen extinction theory then shows that, from interior initial data, the empirical occupation measures concentrate on noninvadable stationary laws, and the Lyapunov exponents of $X_i$ equal the invasion rates there. Thus the deterministic saturated equilibrium of the Ito-shifted system predicts who survives, their long-run mean abundances, and the exponential rates of extinction of the rest.

## Sources

- Jorge Ramirez Osorio, "Coexistence and extinction in stochastic Lotka--Volterra systems with Volterra--Lyapunov stable interactions", arXiv:2610.28174 (2026), Theorem 3, Definition 3 and Lemma 4, <https://doi.org/10.48550/arXiv.2610.28174>
