# Conditional Poisson representation of a randomly driven immigration-death process

Let $Z$ be a continuous-time Markov chain on $E\subseteq\mathbb Z_{\ge0}^d$ (an upstream reaction network evolving autonomously) and let an output species $X$ follow

$$\emptyset\xrightarrow{\lambda(Z(t))}X,\qquad X\xrightarrow{\gamma}\emptyset,$$

with $\gamma>0$ and $\lambda\ge0$ of polynomial growth, $\lambda(z)\le C(1+\|z\|_1)^m$. Call $Z$ **admissible** if it is non-explosive and has a stationary distribution $\pi_Z$ with all polynomial moments finite.

**Proposition (conditional Poisson representation).** Given the path of $Z$, the number of molecules present at time $t$ that were created after time 0 is Poisson with mean $M_t=\int_0^te^{-\gamma(t-u)}\lambda(Z(u))\,du$, independent of the binomially thinned initial molecules. In stationarity (two-sided stationary $Z$), $X(t)$ is conditionally Poisson with mean $M_t=\int_0^\infty e^{-\gamma u}\lambda(Z(t-u))\,du$.

**Corollary (stationary moments).** With $C_\lambda(t)=\operatorname{Cov}_\pi(\lambda(Z(0)),\lambda(Z(t)))$,

$$\mathbb E_\pi X=\frac{\mathbb E_\pi\lambda(Z)}{\gamma},\qquad \operatorname{Var}_\pi X=\mathbb E_\pi X+\frac1\gamma\int_0^\infty e^{-\gamma u}C_\lambda(u)\,du,$$

$$\operatorname{Cov}_\pi(X(0),X(t))=e^{-\gamma t}\,\mathbb E_\pi X+\frac1{2\gamma}\int_0^\infty e^{-\gamma u}\big(C_\lambda(t+u)+C_\lambda(|t-u|)\big)\,du .$$

Admissibility is closed under adjoining such a module: if $Z$ is admissible then so is $(Z,X)$.

**Arithmetic modules.** With $\gamma=1$: identification $A\to A+X$ gives $\mathbb E_\pi X=\mathbb E_\pi A$; addition $A\to A+X$, $B\to B+X$ gives $\mathbb E_\pi A+\mathbb E_\pi B$; multiplication $A+B\to A+B+X$ gives $\mathbb E_\pi X=\mathbb E_\pi[AB]$, which equals $\mathbb E_\pi A\cdot\mathbb E_\pi B$ when the inputs are independent under $\pi$. Hence these modules compute correctly at the level of stationary means, and composing them computes polynomials. If the input mean converges at exponential rate $\rho_A$, the output mean converges at rate at least $\min(\rho_A,1)$.

## Expansion

Each molecule of $X$ is created at the time-varying rate $\lambda(Z(u))$ and survives an independent $\mathrm{Exp}(\gamma)$ lifetime, so conditional on $Z$ the surviving molecules form a thinned inhomogeneous Poisson process (a Cox process). Taking expectations of the conditional Poisson mean and variance gives the law of total variance: Poisson noise $\mathbb E M$ plus the variance of the filtered input $M$, which is the exponentially smoothed autocovariance of $\lambda(Z)$. Because the computed value is a mean, the readout requires averaging a trajectory, and the cost of this averaging is set by the stationary variance and the decay of the autocovariance.

## Sources

- D. F. Anderson, S. Moon, "Mean-level arithmetic computation via stochastic reaction networks", arXiv:2611.11069 (2026), Section 3.1 (modules), Section 4 (Definition 4.1, Condition 4.1, Propositions 4.1 and 4.3, Corollaries 4.2 and 4.4, Theorem 4.5) and Section 5 (Lemmas 5.1, 5.9-5.11), <https://doi.org/10.48550/arXiv.2611.11069>.
