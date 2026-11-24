# Lidskii's inequality

Let $A$ and $B$ be Hermitian complex square matrices of size $N$, with eigenvalues $\alpha_1 \ge \dots \ge \alpha_N$, $\beta_1 \ge \dots \ge \beta_N$ and $\gamma_1 \ge \dots \ge \gamma_N$ of $A$, $B$ and $B - A$, each listed with multiplicity in decreasing order. Then for every real $p \ge 1$,

$$\sum_{j=1}^N |\alpha_j - \beta_j|^p \le \sum_{j=1}^N |\gamma_j|^p.$$

## Idea

How far can the eigenvalues of a Hermitian matrix move under a Hermitian perturbation? Weyl's inequality bounds each eigenvalue separately by the norm of the perturbation. Lidskii's theorem says much more: the vector $\beta - \alpha$ of eigenvalue differences is majorized by the eigenvalue vector $\gamma$ of $B - A$, and when $x$ is majorized by $y$, $\sum_j \varphi(x_j) \le \sum_j \varphi(y_j)$ for every convex function $\varphi$; the function $\varphi(t) = \lvert t\rvert^p$ gives the inequality above. For $p = 2$ this gives the Hoffman–Wielandt inequality for Hermitian matrices. Since $\sum_j |\gamma_j|$ is at most the sum of the absolute values of the entries of $B - A$, the case $p = 1$ gives the Lidskii–Last bound of the $\ell^1$ distance between the spectra by that entrywise sum.

## Statements

- [Lidskii's inequality](lidskii-inequality.md)
- [Lidskii–Last theorem](lidskii-last.md): a weaker form, from the case $p = 1$: the $\ell^1$ distance between the spectra is at most the sum of the absolute values of the entries of $A - B$ (Lidskii–Last)
