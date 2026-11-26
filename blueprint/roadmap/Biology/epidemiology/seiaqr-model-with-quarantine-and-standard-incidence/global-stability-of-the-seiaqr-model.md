# Global stability of the SEIAQR quarantine model

**Setting.** Consider the [SEIAQR model with quarantine and standard incidence](uniform-persistence-of-the-seiaqr-model-with-explicit-lower-bounds.md), with control reproduction number $\mathcal R_c$, disease-free equilibrium $V^0 = (\lambda/d,0,0,0,0,0)$ and, when $\mathcal R_c > 1$, endemic equilibrium $V^*$. Let $D = \{\varphi \in \mathbb R_+^6 : \sum_i \varphi_i > 0\}$ and let $\Omega \subset D$ be the set of initial data with positive infected compartments.

**Theorem (threshold dynamics).**
1. $V^0$ is globally asymptotically stable in $D$ if $\mathcal R_c < 1$, and globally attractive in $D$ if $\mathcal R_c = 1$.
2. If $\mathcal R_c > 1$, then $V^*$ is locally asymptotically stable, the system is weakly persistent ($\limsup_{t\to\infty} E(t) > \theta E^*$ for every $\theta \in (0,1)$), and $V^*$ is globally asymptotically stable in $\Omega$; conversely, global asymptotic stability of $V^*$ in $\Omega$ holds only if $\mathcal R_c > 1$.

**Short-term model.** Dropping births and natural deaths ($\lambda = d = 0$), so that $N$ is a constant $\mathcal N$, every $\omega$-limit point lies in $\{S + R = \mathcal N,\ E = I = A = Q = 0\}$: the epidemic always dies out, with a final size given by the limiting value of $S$. The disease-free states are $\tilde V = (\tilde S, 0,0,0,0, \mathcal N - \tilde S)$, $0 \le \tilde S \le \mathcal N$, with control reproduction number
$$\mathcal R_c(\tilde S) = \frac{\tilde S}{\mathcal N}\Big[\frac{a\beta}{c} + \frac{p\beta}{q_1 + r_1} + \frac{b\beta(1-p)}{q_2 + r_2}\Big];$$
$(0,0,0,0,0,\mathcal N)$ is stable, and for $\tilde S \in (0, \mathcal N]$ the state $\tilde V$ is stable if $\mathcal R_c(\tilde S) \le 1$ and unstable if $\mathcal R_c(\tilde S) > 1$ (relative to $\tilde S > 0$).

## Expansion

Since $\dot N = \lambda - dN$, the total population converges to $\lambda/d$, so the long-term behaviour is governed by the limit system with $N \equiv \lambda/d$ (an asymptotically autonomous system). For $\mathcal R_c \le 1$ a Lyapunov function on the infected compartments together with LaSalle's invariance principle gives convergence to $V^0$. Local stability of $V^*$ is shown by contradiction: a characteristic root with nonnegative real part would force an identity between moduli of complex expressions that cannot hold. Weak persistence (an upper limit of $E$ bounded away from zero) combined with a Lyapunov argument then yields global attractivity of $V^*$ when $\mathcal R_c > 1$.

## Sources

- S. Guo, Y. Xue, X. Li, Z. Zheng, "Dynamics of COVID-19 models with asymptomatic infections and quarantine measures", arXiv:2209.05240 (2022), Theorem 2.1, Theorem 3.1 and Corollary 3.1, Theorems 4.1–4.2 (Section 4), Theorems 5.1–5.3 (Section 5), <https://doi.org/10.48550/arXiv.2209.05240>.
