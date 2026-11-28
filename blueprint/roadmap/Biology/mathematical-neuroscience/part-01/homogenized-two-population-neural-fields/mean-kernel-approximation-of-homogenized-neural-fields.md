# Mean-kernel approximation and global attractor of the homogenized two-population neural field

Let $u_e(x,y,t)$ and $u_i(x,y,t)$ be excitatory and inhibitory membrane potentials at macroscopic position $x \in \mathbb{R}$ and microscopic position $y \in \mathbb{T} = \mathbb{R}/\mathbb{Z}$. The homogenized two-population neural field (the two-scale limit of a Hopfield-type field with periodically modulated connectivity) is

$$\partial_t u_e = -u_e + \omega_{ee} \otimes\otimes P_e(u_e - \theta_e) - \omega_{ie} \otimes\otimes P_i(u_i - \theta_i),$$

$$\tau\,\partial_t u_i = -u_i + \omega_{ei} \otimes\otimes P_e(u_e - \theta_e) - \omega_{ii} \otimes\otimes P_i(u_i - \theta_i),$$

where $(\omega \otimes\otimes P)(x,y,t) = \int_{\mathbb{R}}\int_{\mathbb{T}} \omega(x - x', y - y') P(u(x',y',t))\,dy'\,dx'$ and $\tau > 0$ is the relative inhibition time. Hypotheses: $P_q(u) = S(\beta_q u)$ with $S : \mathbb{R} \to [0,1]$ continuously differentiable with $S'$ bounded and $S' \ge 0$, $S'_{max} = \sup S'$ (so $S$ is Lipschitz with constant $S'_{max}$), as in the source's Eq. (6); $\omega_{qp}(x,y) = \sigma_{qp}(y)^{-1}\,\Phi\big(x/\sigma_{qp}(y)\big)$ with $\Phi$ even, nonnegative, $\int\Phi = 1$, $\int |\xi|^r\Phi(\xi)\,d\xi < \infty$ for some $r \ge 1$, and $\sigma_{qp} > 0$ continuous, $1$-periodic and $C^r$ in $y$. The phase space is $B \times B$ with $B = BC(\mathbb{R} \times \mathbb{T})$ and the sup norm.

**Boundedness and global attractor.** Let $u_q^{(0)}(t) = U_q e^{-t/\tau_q}$ ($\tau_e = 1$, $\tau_i = \tau$) be the solution with the nonlocal terms removed. Then $\|u_q - u_q^{(0)}\|_B(t) \le 1 - e^{-t/\tau_q}$. In particular, if $|U_q| \le 1$ initially then $|u_q| \le 1$ for all $t \ge 0$, and the set $\{|u_q| \le 1\}$ is a global attractor; every instability saturates.

**Theorem (continuous dependence on the kernels).** Let $\langle\omega_{qp}\rangle(x) = \int_{\mathbb{T}} \omega_{qp}(x,y)\,dy$, let $U_{\langle\rangle}$ solve the translation-invariant field with kernels $\langle\omega_{qp}\rangle$, and let $D(t) = \|U - U_{\langle\rangle}\|_{B \times B}(t)$. With $\Delta K_{qp} = \int_{\mathbb{R}}\int_{\mathbb{T}} |\omega_{qp}(x,y) - \langle\omega_{qp}\rangle(x)|\,dy\,dx$ and $\beta_{max} = \max(\beta_e, \beta_i)$, for every finite $T$

$$D(T) \le M(T)\exp\!\Big[\big(1 + \tfrac{1}{\tau}\big)\beta_{max} S'_{max} T\Big], \qquad M(T) = D(0) + \Big[\Delta K_{ee} + \Delta K_{ie} + \tfrac{1}{\tau}\big(\Delta K_{ei} + \Delta K_{ii}\big)\Big] T.$$

Hence in the shallow firing-rate regime $(1 + 1/\tau)\beta_{max} S'_{max} T \ll 1$ and for weak microstructure (small $\Delta K_{qp}$) the homogenized dynamics is approximated over finite times by the translation-invariant model with averaged kernels.

## Expansion

Normalization of the kernels and $0 \le S \le 1$ give $0 \le \omega_{qp} \otimes\otimes P_q \le 1$, so each equation is a linear decay driven by a forcing in $[0,1]$; variation of constants gives the comparison bound. For the theorem, subtract the two systems, split each nonlocal difference into a kernel difference (bounded by $\Delta K_{qp}$ since $0 \le P \le 1$) and a firing-rate difference (bounded by $\beta_q S'_{max}$ times the sup-norm difference, using $\int\int \omega_{qp} = 1$), integrate in time and apply Gronwall's inequality.

## Sources

- K. Kolodina, J. Wyller, A. Oleynik, M. P. Sorensen, Pattern formation in a 2-population homogenized neuronal network model, Journal of Mathematical Neuroscience (2021), Section 2 (Eqs. 4 to 19, Theorem 1) and Appendix A (Lemma 1). <https://doi.org/10.1186/s13408-021-00107-1> PMCID: PMC8236021
