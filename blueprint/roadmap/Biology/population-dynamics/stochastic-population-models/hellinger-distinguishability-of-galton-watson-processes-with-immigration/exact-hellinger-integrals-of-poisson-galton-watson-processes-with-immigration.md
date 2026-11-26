# Exact Hellinger integrals of Poisson Galton–Watson processes with immigration

**Model.** Under a law $P_\bullet$ ($\bullet\in\{A,H\}$), the population $X_n$ is a Galton–Watson process with immigration: given $X_{n-1}=x$, each of the $x$ individuals has Poisson($\beta_\bullet$) offspring and an independent Poisson($\alpha_\bullet$) number of immigrants arrives, so that $X_n\mid X_{n-1}=x\sim\mathrm{Poisson}(\alpha_\bullet+\beta_\bullet x)$; $X_0=\omega_0\in\mathbb{N}$. Any criticality ($\beta_\bullet<1$, $=1$, $>1$) is allowed. Let $P_{\bullet,n}$ be the law of $(X_0,\dots,X_n)$ and, for $\lambda\in(0,1)$, the **Hellinger integral** $H_\lambda(P_{A,n}\|P_{H,n})=\mathbb{E}_{P_{H,n}}\big[(dP_{A,n}/dP_{H,n})^\lambda\big]$, which determines the power divergences, the Rényi divergences and (as $\lambda\to1$) the relative entropy.

Write $\beta_\lambda=\lambda\beta_A+(1-\lambda)\beta_H$, $\alpha_\lambda=\lambda\alpha_A+(1-\lambda)\alpha_H$, $q_\lambda=\beta_A^\lambda\beta_H^{1-\lambda}$, and define recursively

$$a_0=0,\qquad a_n=q_\lambda\,e^{a_{n-1}}-\beta_\lambda\quad(n\ge1).$$

**Theorem.** Suppose either there is no immigration ($\alpha_A=\alpha_H=0$, $\beta_A\ne\beta_H$), or all parameters are positive with $\beta_A/\beta_H=\alpha_A/\alpha_H\ne1$. Then for all $\omega_0$ and $n$,

$$H_\lambda(P_{A,n}\|P_{H,n})=\exp\Big\{a_n\,\omega_0+\frac{\alpha_A}{\beta_A}\sum_{k=1}^n a_k\Big\},$$

and this sequence is strictly decreasing in $n$. For general parameters, replacing $\varphi_\lambda(x)=(\alpha_A+\beta_Ax)^\lambda(\alpha_H+\beta_Hx)^{1-\lambda}$ by linear minorants and majorants $p+qx$ gives recursively computable lower and upper bounds of the same form.

**Distinguishability.** In the equal-ratio immigration case (and further parameter regions) the two sequences of laws are **entirely separated** as $n\to\infty$ (the Hellinger integral tends to $0$). Without immigration, if $\beta_A\le1$ then $(P_{A,n})$ is **contiguous** to $(P_{H,n})$, while if $\beta_A>1$ the pair is neither contiguous nor entirely separated.

## Expansion

Conditioning on $X_{n-1}=x$, the Poisson likelihood ratio gives $\mathbb{E}\big[(dP_A/dP_H)^\lambda\mid x\big]=\exp\{\varphi_\lambda(x)-\alpha_\lambda-\beta_\lambda x\}$. When $\alpha_H\beta_A=\alpha_A\beta_H$ the exponent is affine in $x$, so one step multiplies by $e^{s x}$; the expectation of $e^{s X_{n-1}}$ for a Poisson GWI is again exponential-affine in $X_{n-2}$, and iterating produces the recursion $a_n=q_\lambda e^{a_{n-1}}-\beta_\lambda$. The limiting behavior of $a_n$ (zero, decreasing to a finite negative limit, or diverging) decides contiguity versus separation. A supercritical population dies out with positive probability, and on extinction the two laws cannot be told apart, which is the intuition for the third regime. The paper also obtains the limits of these quantities when two such processes, with time lags tending to zero, converge to Feller branching diffusions.

## Sources

- Niels B. Kammerer and Wolfgang Stummer, "Some distance bounds of branching processes and their diffusion limits", arXiv:1005.3758 (2010), Section 2 (recursions for $a_n$), Theorem 2.2, Propositions 3.1–3.2 and Corollary 3.6, <https://doi.org/10.48550/arXiv.1005.3758>.
