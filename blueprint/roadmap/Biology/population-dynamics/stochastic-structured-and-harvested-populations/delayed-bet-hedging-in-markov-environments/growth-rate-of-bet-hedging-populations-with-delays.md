# Growth rate of bet-hedging populations with delays

**Setting.** The environment $\epsilon(t)$ is a continuous-time Markov chain on $\{1,\ldots,n\}$ with generator $\Pi = [\pi_{ij}]$. Individuals carry one of $n$ phenotypes; phenotype $k$ grows at rate $g^k_i \ge 0$ in environment $i$ and switches to phenotype $\ell$ at rate $\omega^{k\ell}_i \ge 0$. With $G_i = \operatorname{diag}(g^1_i,\ldots,g^n_i)$, $\Omega_i = [\omega^{k\ell}_i]$ ($\omega^{kk}_i = -\sum_{\ell\ne k}\omega^{k\ell}_i$) and $A_i = G_i + \Omega_i^\top$, the delay-free **bet-hedging model** is $\dot x = A_{\epsilon(t)}x$. Two delayed extensions are considered:

$$\Sigma_1:\ \dot x_k = g^k_{\epsilon(t)}x_k + \sum_\ell \omega^{\ell k}_{\epsilon(t)}x_\ell + p^k_{\epsilon(t)}x_k\big(t - d^k_{\epsilon(t)}\big) + \int_0^\infty q^k_{\epsilon(t)}(\tau)\,x_k(t-\tau)\,d\tau,$$

with delayed proliferation ($p \ge 0$, $q \ge 0$ of finite support), and $\Sigma_2:\ \dot x_k = g^k_{\epsilon(t)}x_k + \sum_\ell \omega^{\ell k}_{\sigma(t)}x_\ell$ with delayed adaptation, where the population's information $\sigma$ catches up with $\epsilon$ after a random response delay $T_{ij}$ that restarts if the environment changes first. The **growth rate** is the infimum of $\lambda$ such that $\mathbb E\big[\sum_k x_k(t)\big] \le Ce^{\lambda t}\sum_k\lVert\phi_k\rVert$ for all initial histories $\phi$ and initial environments.

**Theorem.**
1. (Delayed proliferation, Theorem 3.1) Let $u_i$ be the $i$-th unit vector, $U_{ji} = u_ju_i^\top$, $\bar A_0 = \Pi^\top\otimes I_n + \bigoplus_{i=1}^n A_i$, and for $\lambda \in \mathbb R$ let $\bar A^{(\lambda)}_{ij} = u_i \otimes \big(p^j_i e^{-\lambda d^j_i}(U_{ji}e^{\Pi^\top d^j_i}) \otimes u_j^\top\big)$ and $\bar B^{(\lambda)}_{ij}(t) = u_i \otimes \big(q^j_i(t)e^{-\lambda t}(U_{ji}e^{\Pi^\top t}) \otimes u_j^\top\big)$. If

$$\bar T^{(\lambda)} = \bar A_0 - \lambda I + \sum_{i,j}\bar A^{(\lambda)}_{ij} + \sum_{i,j}\int_0^\infty \bar B^{(\lambda)}_{ij}(t)\,dt$$

is Hurwitz, then the growth rate of $\Sigma_1$ is less than $\lambda$; a bisection over $\lambda$ gives an upper bound. Without delays the condition is also necessary, so the growth rate of $\dot x = A_{\epsilon(t)}x$ is the largest real eigenvalue of the Metzler matrix $\Pi^\top \otimes I_n + \bigoplus_i A_i$ (Remark 3.2).
2. (Delayed adaptation, Theorem 4.3) For $n = 2$, if the response delays $T_{12}$ and $T_{21}$ have Coxian (phase-type) distributions with $s$ phases (Assumption 4.1), then $(\epsilon,\sigma)$ is a function of a finite Markov chain $\theta$ with $2s+2$ states and generator $\Xi$ (Proposition 4.2), and the growth rate of $\Sigma_2$ equals the largest real eigenvalue of

$$\Xi^\top \otimes I_2 + \bigoplus_{\theta} A_{(\epsilon(\theta),\sigma(\theta))}, \qquad A_{(i,j)} = G_i + \Omega_j^\top.$$

## Expansion

Because all coefficients are nonnegative off the diagonal, the expected population vector conditioned on the current environment, obtained by stacking $\mathbb E[\mathbf 1\{\epsilon(t)=i\}\,x(t)]$ over $i$,, satisfies a deterministic positive linear delay system (Proposition 3.6), and its norm equals $\mathbb E\lVert x(t)\rVert$ (Lemma 3.3). Exponential stability of positive delay systems is decided by a single Hurwitz test on the matrix obtained by summing all delayed coefficients (Proposition 1.1); shifting by $e^{-\lambda t}$ turns this into a growth-rate bound. For delayed adaptation, phase-type delays make the pair (environment, information) Markov on an enlarged state space, so the growth rate is again the spectral abscissa of a Metzler matrix. The resulting formulas let one compare bet-hedging strategies (phenotype switching rates) by their long-run growth in a fluctuating environment and quantify how proliferation and response delays change that growth.

## Sources

- Masaki Ogura, Masashi Wakaiki and Victor M. Preciado, "Dynamic analysis of bet-hedging strategies as a protection mechanism against environmental fluctuations", arXiv:1603.04682 (2016), Section 2 (models $\Sigma_0$, $\Sigma_1$, $\Sigma_2$ and Definition 2.1), Proposition 1.1, Theorem 3.1, Remark 3.2, Lemma 3.3, Proposition 3.6, Assumption 4.1, Proposition 4.2, Theorem 4.3, <https://doi.org/10.48550/arXiv.1603.04682>. Published version: 2016 IEEE 55th Conference on Decision and Control (CDC) (2016) 4178–4183, <https://doi.org/10.1109/CDC.2016.7798903>.
