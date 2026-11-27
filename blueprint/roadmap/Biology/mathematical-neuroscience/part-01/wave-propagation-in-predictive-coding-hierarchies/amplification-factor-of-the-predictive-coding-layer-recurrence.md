# Amplification factor of the predictive-coding layer recurrence

**Model.** With identity feedforward and feedback weights, the activity $e_j^n\in\mathbb R$ of layer $j$ at time step $n$ in a predictive-coding hierarchy evolves on an infinite-depth network by

$$e_j^{n+1}=\beta e_{j-1}^{n+1}+\alpha e_{j-1}^{n}+(1-\beta-\lambda-\alpha)e_j^{n}+\lambda e_{j+1}^{n},\qquad j\in\mathbb Z,$$

where $\beta$ weighs instantaneous feedforward drive, $\alpha$ feedforward prediction errors and $\lambda$ feedback predictions, with $0\le\beta<1$ and $0\le\alpha+\lambda\le1$.

**Amplification factor.** Plane waves $\rho(\theta)^ne^{ij\theta}$ solve the recurrence with

$$\rho(\theta)=\frac{\alpha(e^{-i\theta}-1)+1-\beta+\lambda(e^{i\theta}-1)}{1-\beta e^{-i\theta}},\qquad\theta\in[-\pi,\pi],$$

and the fundamental solution from a unit impulse is $G_j^n=\frac1{2\pi}\int_{-\pi}^{\pi}e^{ij\theta}\rho(\theta)^n\,d\theta$, with every solution $e_j^n=\sum_\ell G_{j-\ell}^nh_\ell$. Since $\lim_n\|G^n\|_{\ell^1}^{1/n}=\max_\theta|\rho(\theta)|$, the recurrence is stable if $|\rho|<1$ everywhere and unstable if $|\rho(\theta_0)|>1$ somewhere.

**Proposition.** For $0\le\beta<1$ and $\alpha,\lambda\ge0$: $\rho(0)=1$, and $|\rho(\theta)|\le1$ for all $\theta$ iff $\alpha+\lambda\le1$. Excluding the degenerate unit-modulus cases $\alpha=\lambda=\beta=0$ and $\{\alpha,\lambda\}=\{0,1\}$ (equivalently, assuming the source's standing hypothesis $\sigma_0>0$), if $\alpha+\lambda<1$, then $|\rho(\theta)|<1$ for $\theta\ne0$; if $\alpha+\lambda=1$, then also $\rho(\pm\pi)=-1$ and $|\rho(\theta)|<1$ for $\theta\notin\{0,\pm\pi\}$. When the tangency points satisfy $\rho(\theta_k+\theta)/\rho(\theta_k)=\exp(-ic_k\theta-\sigma_k\theta^{2\mu_k}+O(|\theta|^{2\mu_k+1}))$ with $\operatorname{Re}\sigma_k>0$, the recurrence is marginally stable: $\sup_j|e_j^n|\le C\sup_j|h_j|$ for all $n$.

## Expansion

A direct computation gives that $|\rho(\theta)|^2\le1$ is equivalent to $(1-\cos\theta)\big[2\beta+4\alpha\lambda\cos\theta+2(1-\beta)(\lambda+\alpha)-2(\lambda^2+\alpha^2)\big]\ge0$; the bracket is smallest at $\cos\theta=-1$, where it equals $2[\beta+(1-\beta)(\lambda+\alpha)-(\lambda+\alpha)^2]=2(\beta+\lambda+\alpha)(1-\lambda-\alpha)$, so it is nonnegative for all $\theta$ iff $(\beta+\lambda+\alpha)(1-\lambda-\alpha)\ge0$, that is iff $\alpha+\lambda\le1$, and outside the degenerate cases $\alpha=\lambda=\beta=0$ and $\{\alpha,\lambda\}=\{0,1\}$ (where $\alpha\lambda=0$ makes the bracket identically zero and $|\rho(\theta)|\equiv1$), equality occurs only at $\theta=0$ or at $\theta=\pm\pi$ with $\alpha+\lambda=1$. Marginal stability is the biologically relevant regime: activity neither dies out uniformly nor runs away.

## Sources

- G. Faye, G. Fouilhé, R. VanRullen, "Mathematical derivation of wave propagation properties in hierarchical neural networks with predictive coding feedback dynamics", Bulletin of Mathematical Biology 85 (2023), Sections "The Identity Case", "Wave Propagation on an Infinite Depth Network" and "Study of the Amplification Factor Function": Equations (6), (7), (11)–(14) and Theorem 1, <https://doi.org/10.1007/s11538-023-01186-9>, PMCID PMC10382470.
