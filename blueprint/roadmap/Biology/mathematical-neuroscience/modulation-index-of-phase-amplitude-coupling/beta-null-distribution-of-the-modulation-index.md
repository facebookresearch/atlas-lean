# Beta null distribution of the modulation index

**Modulation index.** From a low-frequency signal take its instantaneous phase $\phi_{LF}(n)$ and from a high-frequency signal its instantaneous amplitude $A_{HF}(n)$ (both via the analytic signal). Split $[0,2\pi)$ into $B$ equal bins and let

$$P(b)=\frac{\overline{A_{HF}}\ \text{over samples with}\ \phi_{LF}\in\text{bin }b}{\sum_{b'=0}^{B-1}\overline{A_{HF}}\ \text{over samples with}\ \phi_{LF}\in\text{bin }b'},\qquad H_P=-\sum_bP(b)\log_KP(b).$$

The modulation index is

$$\rho_{\rm MI}=\frac{D_{KL}(P\,\|\,U)}{\log_KB}=1-\frac{H_P}{\log_KB}\in[0,1],$$

with $U$ the uniform distribution on bins; $\rho_{\rm MI}=0$ iff the amplitude profile is flat.

**Null model.** For independent white Gaussian signals $X_1,\dots,X_N$ and $Y_1,\dots,Y_N$, the amplitude of one is approximately Rayleigh and independent of the phase of the other, and phases fall uniformly into the $B$ bins. The bin means are then averages of a binomial number of Rayleigh variables, and each normalized bin value $p_b$ has approximately

$$\mu_p=\frac1B,\qquad \sigma_p^2=B\Big(1-\frac1B\Big)\Big(\frac1{B^3}+\frac{\frac4\pi-1}{N}\Big(\frac1{B^2}+\frac{1-\frac1B}{N}\Big(\frac1B-\frac{1-\frac2B}{2N}\Big)\Big)\Big).$$

**Theorem.** In this null model, $\rho_{\rm MI}$ is approximately beta distributed, with shape parameters $b_{MI}=\mu_HD_H$ and $a_{MI}=(1-\mu_H)D_H$, $D_H=(\mu_H-\mu_H^2)/\sigma_H^2-1$, where the moments $\mu_H,\sigma_H^2$ come from a Dirichlet approximation of $(p_b)$ with parameter $a_p=\mu_p\big((\mu_p-\mu_p^2)/\sigma_p^2-1\big)$:

$$\mu_H=-BM_1,\qquad \sigma_H^2=B(M_2-M_1^2)+B(B-1)C,$$

$$M_1=\tfrac1B\,h(a_p,1,1),\quad M_2=\tfrac1B\,\tfrac{a_p+1}{Ba_p+1}\big(h'(a_p,2,2)+h(a_p,2,2)^2\big),\quad C=\tfrac1B\big(\psi^{(1)}(Ba_p+2)+h(a_p,1,2)^2\big),$$

with $h(a,i,j)=\psi(a+i)-\psi(Ba+j)$ and $\psi$ the digamma function. Comparing an observed index against this law (or comparing two indices) gives a hypothesis test for coupling that accounts for finite $N$ and $B$.

## Expansion

If $(p_b)\sim\mathrm{Dirichlet}(a_p,\dots,a_p)$, then $\mathbb E[p\log p]$ and the second moments of $p_b\log p_b$ are digamma expressions, which gives the mean and variance of the entropy $H_P$ in closed form; matching a beta law to those two moments yields the shape parameters. The key point is that independent noise produces a strictly positive expected index of order $B/N$, so thresholding $\rho_{\rm MI}$ against $0$, or against a uniform reference, overstates coupling.

## Sources

- M. A. Pinto-Orellana, H. Ombao, B. Lopour, "Statistical Inference for Modulation Index in Phase-Amplitude Coupling", arXiv:2310.05398 (2023), Section 2.1 (Eq. (mod-index)), Section 2.3 (lemmas on Rayleigh averages and histogram moments, theorem on the modulation-index distribution), Section 2.4, <https://doi.org/10.48550/arXiv.2310.05398>.
