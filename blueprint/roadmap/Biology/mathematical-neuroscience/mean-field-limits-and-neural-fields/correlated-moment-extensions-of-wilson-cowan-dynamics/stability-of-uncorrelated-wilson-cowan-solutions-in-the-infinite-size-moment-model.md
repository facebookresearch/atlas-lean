# Stability of uncorrelated Wilson–Cowan solutions in the infinite-size moment model

**Model.** $M$ neural populations with Markovian (quiescent/active) firing, effective weights $w_{ij}$, decay rates $\alpha_i>0$, inputs $I_i$ and smooth sigmoidal gain functions $f_i$. Truncating the moment hierarchy of the master equation at second order (Bressloff's system-size expansion, or the Buice–Cowan normal-ordered cumulant expansion) and letting the population sizes $N_i\to\infty$ in the rescaled variables, both closures converge to the **infinite-size model** for the mean activities $\nu_i$ and the correlations $\Delta_{ij}$:

$$
\begin{aligned}
\dot\nu_i&=-\alpha_i\nu_i+f_i(s_i)+\tfrac12 f_i''(s_i)\sum_{k,l}w_{ik}w_{il}\Delta_{kl},\qquad s_i=\sum_j w_{ij}\nu_j+I_i,\\
\dot\Delta_{ij}&=-(\alpha_i+\alpha_j)\Delta_{ij}+\sum_k\big[f_i'(s_i)w_{ik}\Delta_{kj}+f_j'(s_j)w_{jk}\Delta_{ki}\big].
\end{aligned}
$$

With $\Delta\equiv0$ the mean equation is the Wilson–Cowan (WC) system $\dot\nu_i=-\alpha_i\nu_i+f_i(s_i)$. For finite $N_i$ the Bressloff closure adds the source $\frac{1}{N_i}[\alpha_i\nu_i+f_i(s_i)]\delta_{ij}$ to the correlation equation (the Buice–Cowan closure adds terms of order $1/N_j$ proportional to $f_i'(s_i)w_{ij}\nu_j$), which unfolds the degenerate bifurcations of the infinite-size model.

**Lemma (Touboul–Ermentrout, Lemma 1).** Let $A(x)=-\operatorname{diag}(\alpha)+F(x)$ with $F_{ij}(x)=f_i'\big(\sum_k w_{ik}x_k+I_i\big)w_{ij}$, the Jacobian of the WC vector field. Then $\dot\Delta=A(\nu)\Delta+\Delta A(\nu)^{\mathsf T}$, i.e. $V_\Delta=\operatorname{vec}(\Delta)$ satisfies

$$
\dot V_\Delta=\big(A(\nu(t))\oplus A(\nu(t))\big)V_\Delta,\qquad A\oplus A=A\otimes I_M+I_M\otimes A .
$$

**Theorem (Touboul–Ermentrout, Theorem 1).** Every WC solution $\nu(t)$ gives a solution $(\nu(t),\Delta\equiv0)$ of the infinite-size model, and:

1. a zero-correlation fixed point $(\nu^*,0)$ is exponentially stable (resp. exponentially unstable, neutrally stable) if and only if $\nu^*$ is so for the WC system; the spectrum of the Jacobian is $\{\lambda_i\}\cup\{\lambda_i+\lambda_j\}$, where $\lambda_1,\dots,\lambda_M$ are the WC eigenvalues at $\nu^*$;
2. a zero-correlation cycle $(\nu(t),0)$ is exponentially unstable if and only if $\nu(t)$ is an unstable WC cycle; if $\nu(t)$ is a stable WC cycle, $(\nu(t),0)$ has only **neutral** linear stability. Hence the infinite-size model has no exponentially stable cycle with zero correlations.

In the one-population case (Proposition 1) the eigenvalues at $(\nu^*,0)$ are $\lambda$ and $2\lambda$ with $\lambda=-\alpha+wf'(w\nu^*+I)$. At a WC Hopf point with eigenvalues $\pm i\omega$, the two-population infinite-size Jacobian has the five eigenvalues $\pm i\omega,\pm2i\omega,0$, all on the imaginary axis: a highly degenerate point from which correlation-induced cycles can emerge.

## Proof sketch

At $\Delta=0$ the Jacobian is block upper-triangular: the $\nu$ block is the WC Jacobian $A(\nu)$ and the $\Delta$ block is $A\oplus A$, whose eigenvalues are the pairwise sums $\lambda_i+\lambda_j$. For a $T$-periodic WC orbit, the fundamental matrix of the correlation equation is $\Psi(t)=\Phi(t)\otimes\Phi(t)$, where $\Phi$ is the WC fundamental matrix, so the Floquet multipliers are the products $\mu_i\mu_j$. A periodic orbit always has the trivial multiplier $\mu=1$ (eigenvector $\dot\nu(0)$), so $\Psi(T)$ has the multiplier $1$ with eigenvector $\operatorname{vec}(\dot\nu(0)\dot\nu(0)^{\mathsf T})$ in the correlation directions, which removes exponential stability; an unstable multiplier $|\mu_i|>1$ gives $|\mu_i^2|>1$.

## Sources

- Jonathan D. Touboul and G. Bard Ermentrout, "Finite-size and correlation-induced effects in mean-field dynamics", *Journal of Computational Neuroscience* 31 (2011), 453–484, <https://doi.org/10.1007/s10827-011-0320-5>. Preprint version: arXiv:1008.2839 (2010), <https://doi.org/10.48550/arXiv.1008.2839>.
