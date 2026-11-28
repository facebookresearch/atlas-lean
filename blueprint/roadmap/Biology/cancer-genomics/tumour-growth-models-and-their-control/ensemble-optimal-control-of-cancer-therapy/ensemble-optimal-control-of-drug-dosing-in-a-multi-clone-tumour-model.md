# Ensemble optimal control of drug dosing in a multi-clone tumour model

**Setting.** A tumour consists of $n$ subpopulations $X = (X_1,\dots,X_n)$ with total $N = \sum_i X_i$, logistic growth rates $r_i > 0$, common carrying capacity $K$, turnover rates $d_i^T \ge 0$, drug sensitivities $d_i^I \ge 0$, and spontaneous and drug-induced switching matrices $A, A^I$ (nonnegative off-diagonal, columns summing to zero, so switching conserves cells). Under a dose $D(t) \in [0,D_{\max}]$,

$$\dot X_i = r_i\Big(1 - \frac{N}{K}\Big)\Big(1 - \frac{2 d_i^I}{D_{\max}} D\Big) X_i - d_i^T X_i + \sum_j \Big(A_{ij} + \frac{A^I_{ij}}{D_{\max}} D\Big) X_j, \qquad X_i(0) = f_i N_0,$$

which is control-affine, $\dot X^\theta = F_0^\theta(X^\theta) + F_1^\theta(X^\theta)\,D$, in the uncertain parameter vector $\theta = (r, K, d^I, d^T, A, A^I, f, N_0)$ ranging over a compact set $\Theta$ on which $f_i \ge 0$, $\sum_i f_i = 1$, $K \in [K_{\min}, K_{\max}]$ with $K_{\min} > 0$, and $0 \le N_0 \le K$. Parameter uncertainty is described by a probability measure $\mu$ on $\Theta$, and the **averaged ensemble cost** for a $C^2$ penalty $\ell \ge 0$ on tumour size is

$$\mathcal{J}(D) = \int_\Theta \int_0^T \ell\big(N_D^\theta(t)\big)\,dt\,d\mu(\theta), \qquad D \in \mathcal{U} = \{D \in L^2(0,T) : 0 \le D \le D_{\max}\}.$$

**Theorem.**
1. (Invariance.) For every $\theta$, the set $\{X \ge 0,\ \sum_i X_i \le K\}$ is forward invariant.
2. (Existence and $\Gamma$-convergence.) $\mathcal{J}$ has a minimiser on $\mathcal{U}$. If $\mu_k \rightharpoonup^\ast \mu$ (for example, empirical measures of parameter samples) and $D_k^\star$ minimises the corresponding $\mathcal{J}_k$, then $\min_{\mathcal{U}} \mathcal{J} = \lim_k \mathcal{J}_k(D_k^\star)$ and every weak $L^2$ limit point of $(D_k^\star)$ minimises $\mathcal{J}$.
3. (Gradient.) $\mathcal{J}$ is Gateaux differentiable with

$$\nabla_D \mathcal{J}(t) = \int_\Theta g_D^\theta(t)\, F_1^\theta\big(X_D^\theta(t)\big)\,d\mu(\theta),$$

where the covector $g_D^\theta$ solves the backward adjoint equation $\dot g = -\ell'(N)\,\mathbf{1}^\top - g\,(\partial_x F_0^\theta + D\,\partial_x F_1^\theta)$, $g(T) = 0$; moreover projecting $D - \eta\nabla\mathcal{J}$ onto $\mathcal{U}$ equals projecting after first projecting $-\nabla\mathcal{J}$ onto the tangent cone of $\mathcal{U}$.
4. (Bang-bang structure.) An optimal dose minimises $\psi(t)\,v$ over $v \in [0,D_{\max}]$: $D^\star = 0$ where $\psi(t) > 0$ and $D^\star = D_{\max}$ where $\psi(t) < 0$, with switching function $\psi(t) = \int_\Theta g^\theta_{D^\star}(t)\,F_1^\theta(X^\theta_{D^\star}(t))\,d\mu(\theta)$; on a positive-measure set where $\psi = 0$ the control is singular. (The source's Remark 4 states the two cases the other way round; the form here is the one its Proposition 2.5 gives for a minimiser, since $\psi = \nabla\mathcal{J}$.)

## Expansion

Because the drug acts affinely and the admissible doses form a weakly compact convex set in $L^2$, lower semicontinuity of $\mathcal{J}$ along weakly converging doses follows from uniform-in-$\theta$ continuity of the control-to-trajectory map, which gives existence; the same uniform estimates make $\mathcal{J}_k \to \mathcal{J}$ continuously, the hypothesis behind $\Gamma$-convergence, so optimising against a finite sample of plausible patients approximates the problem for the full parameter distribution. The cost depends only on the observable total burden $N$, not on the unobservable clone sizes. The switching function averages the single-patient Pontryagin switching functions over $\mu$, so the ensemble optimum is a compromise schedule rather than the optimum for any one parameter value; numerically it reproduces and improves on threshold-based adaptive therapy by delaying treatment until sensitive cells suppress resistant ones through competition.

## Sources

- Alessandro Scagliotti, Federico Scagliotti, Laura Deborah Locati, Federico Sottotetti, "Ensemble Optimal Control for Managing Drug Resistance in Cancer Therapies", Bulletin of Mathematical Biology 88 (2026), 92, <https://doi.org/10.1007/s11538-026-01661-z>. Published version of arXiv:2503.08927, cited next; locators there refer to the arXiv version.
- Alessandro Scagliotti, Federico Scagliotti, Laura Deborah Locati, Federico Sottotetti, "Ensemble optimal control for managing drug resistance in cancer therapies", arXiv:2503.08927 (2025), Section 2, Lemma 2.1, Theorem 2.2, Remark 4, Lemma 2.4, Proposition 2.5, Corollary 2.6, Lemma 2.7 and Proposition 2.8, <https://doi.org/10.48550/arXiv.2503.08927>.
