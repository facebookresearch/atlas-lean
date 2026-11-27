# Stability in probability of regulatory networks with multiplicative noise

**Model.** Let $x(t) \in \mathbb{R}^n$ be gene-product concentrations measured from an equilibrium (shifted to $0$) and $\omega(t)$ a standard scalar Wiener process. Intrinsic fluctuation of the interaction matrix $N$ is modeled by the Itô equation

$$dx = Nx\,dt + Mx\,d\omega,$$

where $M$ holds the fluctuation amplitudes of the entries of $N$, and in the nonlinear case by $dx = N(x)\,dt + M(x)\,d\omega$ with $N(0) = 0$, $M(0) = 0$.

**Theorem 1 (linear network).** If there is a symmetric positive definite $P$ with

$$PN + N^{\mathsf T}P + M^{\mathsf T}PM \le 0,$$

then the equilibrium $x = 0$ is stable in probability.

**Theorem 2 (nonlinear network).** If there is $V(x) > 0$ for $x \ne 0$, $V(0) = 0$, satisfying the Hamilton–Jacobi inequality

$$\Big(\frac{\partial V}{\partial x}\Big)^{\mathsf T}N(x) + \frac12 M(x)^{\mathsf T}\frac{\partial^2 V}{\partial x^2}M(x) \le 0,$$

then $x = 0$ is stable in probability.

**Polytopic relaxation.** If the Jacobians satisfy $\partial[N(x); M(x)]/\partial x \in \operatorname{Co}\{[N_1; M_1], \dots, [N_L; M_L]\}$ for all $x$ (global linearization), a common $P = P^{\mathsf T} > 0$ with $PN_i + N_i^{\mathsf T}P + M_i^{\mathsf T}PM_i \le 0$ for $i = 1, \dots, L$ certifies stability of the nonlinear network; this is a linear matrix inequality (LMI) feasibility problem, more conservative than Theorem 2 but tractable.

## Expansion

For $V = x^{\mathsf T}Px$ the Itô generator is $\mathcal LV = x^{\mathsf T}(PN + N^{\mathsf T}P + M^{\mathsf T}PM)x$, the extra term $M^{\mathsf T}PM$ coming from the second-order Itô correction; the inequality makes $\mathbb{E}\,V(x(t))$ non-increasing, the stochastic analogue of the Lyapunov condition $PN + N^{\mathsf T}P \le 0$ of the noise-free network. Because $M^{\mathsf T}PM \ge 0$, the condition is strictly harder than the deterministic one: eigenvalues of $N$ close to the imaginary axis are the modes most easily destabilized by intrinsic fluctuations, so their distance from the axis serves as a robustness margin. Theorem 2 is the same computation with a general $V$.

## Sources

- B.-S. Chen and Y.-C. Wang, "On the attenuation and amplification of molecular noise in genetic regulatory networks", BMC Bioinformatics 7 (2006) 52, Eqs. (2)–(10), Theorems 1–2 and Remark 2, <https://doi.org/10.1186/1471-2105-7-52>, PMCID PMC1435772.
