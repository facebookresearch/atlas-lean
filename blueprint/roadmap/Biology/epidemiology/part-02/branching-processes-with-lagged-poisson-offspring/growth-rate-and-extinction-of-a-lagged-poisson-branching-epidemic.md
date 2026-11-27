# Growth rate and extinction probability of a lagged Poisson branching epidemic

**Model.** Let $I_n$ be the number of new cases at time $n$, generated as

$$I_n = \sum_{l=1}^{d}\sum_{i=1}^{I_{n-l}} Y_{n-l,n,i},\qquad Y_{n-l,n,i} \sim \mathrm{Poisson}(\Psi_l)\ \text{independent},$$

where $\Psi_l > 0$ is the mean number of new cases produced with delay $l$ by one case. With $\tilde I_n = (I_n, I_{n-1},\dots,I_{n-d+1})$, $\{\tilde I_n\}$ is a $d$-type Bienaymé–Galton–Watson process with mean matrix

$$\tilde M = \begin{pmatrix}\Psi_1 & 1 & 0 & \cdots & 0\\ \Psi_2 & 0 & 1 & \cdots & 0\\ \vdots & & & \ddots & \\ \Psi_{d-1} & 0 & 0 & \cdots & 1\\ \Psi_d & 0 & 0 & \cdots & 0\end{pmatrix},\qquad \mathbb{E}(\tilde I_n \mid \tilde I_{n-1}) = \tilde I_{n-1}\tilde M,$$

and offspring generating functions $f^{(h)}(s) = s_{h+1}\exp\big(-\Psi_h(1-s_1)\big)$, $s_{d+1} := 1$. Let $R_\infty = \sum_{l=1}^d \Psi_l$.

**Results.**

1. The Perron root $\rho$ of $\tilde M$ is the unique positive solution of $\sum_{l=1}^d \Psi_l\rho^{-l} = 1$, and $\rho \le 1 \iff R_\infty \le 1$.
2. Almost surely $I_n \to 0$ or $I_n \to \infty$. If $R_\infty > 1$ then $I_n/(I_0\rho^n) \to W$ a.s. for a nonnegative integrable $W$ with $\{W > 0\} = \{I_n \to \infty\}$ a.s.; if $R_\infty \le 1$ the epidemic dies out a.s.
3. The extinction probability from initial vector $(I_0, I_{-1},\dots,I_{-(d-1)})$ is $q = q_1^{I_0}q_2^{I_{-1}}\cdots q_d^{I_{-(d-1)}}$ with

$$q_h = \exp\Big(-\sum_{l=h}^{d}\Psi_l\,(1-q_1)\Big),$$

so $q_1$ is the smallest root in $[0,1]$ of $q_1 = e^{-R_\infty(1-q_1)}$: $q_1 = 1$ if $R_\infty \le 1$, and $q_1 < 1$, decreasing in $R_\infty$, if $R_\infty > 1$.

## Expansion

The characteristic polynomial of the companion-type matrix $\tilde M$ is $\lambda^d - \Psi_1\lambda^{d-1} - \dots - \Psi_d$, whose positive root solves $\sum_l\Psi_l\lambda^{-l} = 1$; the left side is decreasing in $\lambda$ and equals $R_\infty$ at $\lambda = 1$, giving item 1. Equivalently, $\tilde M^{\mathsf T}$ is the irreducible Leslie matrix with fertilities $\Psi_1,\dots,\Psi_d$ and all survival coefficients $1$, and item 1 is its Euler–Lotka equation. Items 2 and 3 are the standard dichotomy, Kesten–Stigum-type martingale limit and generating-function fixed-point equations for positively regular multitype processes; a case of type $h$ (an infection $h-1$ steps old) still has delays $h,\dots,d$ ahead of it, so its offspring are Poisson with mean $\sum_{l\ge h}\Psi_l$. The deterministic recursion $X_n = X_{n-1}\tilde M$ has the same threshold, but at $\rho = 1$ it persists while the stochastic process goes extinct. The framework was applied to the BSE epidemic in Great Britain, with $\Psi_l$ depending on control regulations.

## Depends on

- [When R₀ > 1, major outbreaks have positive probability](../../branching-process-approximation-of-early-epidemi/one-sub-extinction-prob-pos.md)

## Proof depends on

- [Perron root of a Leslie matrix](../../../population-dynamics/leslie-matrix-model/exists-perron-root-sum-eq-one.md)

## Sources

- Jacob C, "Branching processes: their role in epidemiology", Int J Environ Res Public Health (2010), Section 5, Propositions 7–11, <https://doi.org/10.3390/ijerph7031204>, PMCID PMC2872325.
