# Asymptotic absolute concentration robustness

**Setting.** A reaction system $\dot X=f(X)$ on $\mathbb R^n_{\ge0}$ (for example mass-action kinetics) evolves within stoichiometric compatibility classes. It has *well-defined dose-response curves for input $X_i$* if, for every $\mathbf x_0\in\mathbb R^n_{>0}$ and all sufficiently large $\lambda$, the compatibility class of $\mathbf x_0+\lambda\mathbf e_i$ contains a unique positive equilibrium $\overline X(\lambda)$; the map $\lambda\mapsto\overline X_j(\lambda)$ is the dose-response curve of $X_j$ with respect to $X_i$. Species $X_j$ has **absolute concentration robustness** (ACR) if its steady-state value is the same in every compatibility class. It has **asymptotic ACR (aACR) with respect to $X_i$** if there is $a_{i,j}>0$ such that $\lim_{\lambda\to\infty}\overline X_j(\lambda)=a_{i,j}$ for every $\mathbf x_0\in\mathbb R^n_{>0}$: the steady state of $X_j$ saturates at a positive level independent of the initial condition as the supply of $X_i$ grows. A *positive conservation law* is a nonnegative vector $w$ with $w\cdot X$ constant along trajectories; its support is $\Sigma=\{X_j:w_j>0\}$.

**Lemma 1.** Let $P(x,\lambda)$ be a real polynomial and $x(\lambda)$ a continuous function with $P(x(\lambda),\lambda)=0$ for all large $\lambda$. Then $\lim_{\lambda\to\infty}x(\lambda)$ exists in $[-\infty,\infty]$. Writing $P(x,\lambda)=\lambda^mq(x)+r(x,\lambda)$ with $m$ the top degree in $\lambda$ and $q\ne0$, a finite limit is a root of $q$.

**Theorem 1 (ubiquity of aACR).** Suppose the system has well-defined dose-response curves for input $X_i$ and admits a positive conservation law with support $\Sigma$ not containing $X_i$. Then some species $X_j\in\Sigma$ has aACR with respect to $X_i$.

**Theorem 2 (criterion).** Under the same assumptions, if $X_j\in\Sigma$ and the leading polynomial $q$ of the steady-state relation $P(x,\lambda)=0$ for $X_j$ has no root at zero, then $X_j$ has aACR with respect to $X_i$.

## Expansion

Steady states of polynomial systems satisfy, after elimination (Gröbner bases or resultants), a single polynomial relation $P(\overline X_j,\lambda)=0$, so by Lemma 1 every dose-response curve has a limit; if finite it is a root of $q$, which does not depend on $\mathbf x_0$. Along the conservation law $w\cdot X$, the total is fixed independently of $\lambda$ because $X_i\notin\Sigma$, so the species in $\Sigma$ stay bounded; they cannot all tend to $0$ while their weighted sum is a fixed positive constant, so at least one converges to a positive root of $q$. Exact ACR is the special case of a constant dose-response curve. Numerically, aACR is practically indistinguishable from ACR under realistic measurement noise and arises in networks without exact ACR motifs, such as the phosphorylation-dephosphorylation futile cycle and the EnvZ-OmpR osmoregulation system.

## Sources

- H. Hong, D. Rojas La Luz, G. Craciun, "Asymptotic robustness in biochemical systems", arXiv preprint (2025), Definition of aACR, Lemma 1 (Section 5.2), Theorem 1 and Theorem 2 (Section 5.2), <https://doi.org/10.48550/arXiv.2505.21900>.
