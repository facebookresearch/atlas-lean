# Steady-state substrate mean under randomly fluctuating catalytic rate

Substrate flows in at rate $k_{\rm in}$ and is converted by an enzyme whose catalytic (degradation) rate fluctuates. This is dynamic disorder. The rate $\gamma(t)$ is a stationary continuous-time Markov chain on states $\gamma_1,\dots,\gamma_n>0$ with generator $Q$ and stationary law $\pi$. Its speed-$c$ version is $\gamma_c(t)=\gamma(ct)$, so $c$ is the speed of enzyme fluctuations relative to substrate kinetics. The substrate obeys $\dot S_c=k_{\rm in}-\gamma_c(t)S_c$, or the analogous birth–death chain for copy numbers. Let $m_{\rm eq}(c)=\lim_{t\to\infty}\mathbb E[S_c(t)]$ and $D=\mathrm{diag}(\gamma_1,\dots,\gamma_n)$.

**Theorem.** For every $c\ge0$, the matrix $D-cQ$ is invertible and

$$
m_{\rm eq}(c)=k_{\rm in}\,\pi^\top(D-cQ)^{-1}\mathbf 1 .
$$

If $\tilde Q=D^{-1}Q$ is diagonalizable with eigenvalues $\lambda_i$, right eigenvectors $u_i$ and left eigenvectors $w_i$, then

$$
m_{\rm eq}(c)=k_{\rm in}\sum_{i=1}^n\frac{\alpha_i}{1-c\lambda_i},\qquad \alpha_i=(\pi^\top u_i)(w_i^\top D^{-1}\mathbf 1).
$$

Moreover, $m_{\rm eq}(c)$ always lies between the deterministic and static limits:

$$
\frac{k_{\rm in}}{\mathbb E_\pi[\gamma]}=\lim_{c\to\infty}m_{\rm eq}(c)\ \le\ m_{\rm eq}(c)\ \le\ \lim_{c\to0}m_{\rm eq}(c)=k_{\rm in}\,\mathbb E_\pi\Big[\frac1\gamma\Big].
$$

So slow conformational fluctuations raise the mean substrate level up to the Jensen gap $\mathbb E_\pi[1/\gamma]-1/\mathbb E_\pi[\gamma]$. This stochastic amplification is set by the relative speed $c$ alone.

## Proof sketch

Solving the linear ODE gives $m_{\rm eq}(c)=k_{\rm in}\int_0^\infty\mathbb E\big[e^{-\int_0^s\gamma_c(u)\,du}\big]\,ds$. By the Feynman–Kac formula the integrand is $\pi^\top e^{s(cQ-D)}\mathbf 1$, and integrating over $s$ gives the resolvent $(D-cQ)^{-1}$. As $c\to\infty$ the time average of $\gamma_c$ tends to $\mathbb E_\pi\gamma$. As $c\to0$, $\gamma_c$ is frozen at its initial value, which has law $\pi$. The sandwich follows from the resolvent formula.

## Related topics

- [Michaelis–Menten kinetics and the quasi-steady-state approximation](../../michaelis-menten-kinetics-and-the-quasi-steady-s/README.md)

## Sources

- Ankit Gupta, Andreas Milias-Argeitis and Mustafa Khammash, "Dynamic disorder in simple enzymatic reactions induces stochastic amplification of substrate", *Journal of The Royal Society Interface* 14 (2017), 20170311, <https://doi.org/10.1098/rsif.2017.0311>. Preprint version: arXiv:1704.08933 (2017), Proposition 2.1 and Theorem 2.2 (Eqs. (mceqform2), (mainmceqformula), (sandwichprop), (mdeterministic), (mstatic)), <https://doi.org/10.48550/arXiv.1704.08933>.
