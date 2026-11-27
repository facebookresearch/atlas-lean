# Jackknife moment closure under selection

Add to the neutral model of the [moment equations](moment-equations-for-the-neutral-sample-frequency-spectrum.md) diploid selection with genotype fitnesses $1$, $1 + hs$, $1 + s$ for $aa$, $aA$, $AA$ (selection coefficient $s$, dominance $h$), so that the frequency density evolves by

$$\partial_t \varphi = \frac{1}{4N}\, \partial_x^2[x(1-x)\varphi] - s\, \partial_x\big[(h + (1-2h)x)\,x(1-x)\,\varphi\big] + 2Nu\,\delta\!\left(x - \tfrac{1}{2N}\right).$$

**Unclosed hierarchy.** Projecting on the binomial weights $w_{n,i}$ as in the neutral case gives, for $1 \le i \le n-1$ and $n|s| \ll 1$,

$$\dot\Phi_n(i) = \frac{1}{4N}\big(\tilde\Delta_n \Phi_n\big)(i) + \frac{sh}{n+1}\Big[i(n+1-i)\Phi_{n+1}(i) - (n-i)(i+1)\Phi_{n+1}(i+1)\Big]$$

$$\qquad + \frac{s(1-2h)(i+1)}{(n+1)(n+2)}\Big[i(n+1-i)\Phi_{n+2}(i+1) - (n-i)(i+2)\Phi_{n+2}(i+2)\Big] + U_n(i),$$

where $\tilde\Delta_n$ is the neutral drift operator and $U_n(i) = 2Nu\binom{n}{i}(2N)^{-i}(1 - \tfrac{1}{2N})^{n-i}$ is the exact projection of the point source, as in the neutral case. To leading order in $1/N$, $U_n(i) = nu\,\delta_{i,1}$, the form used below. The selection term needs the spectrum at sample sizes $n+1$ and $n+2$, whose equations need $n+3$ and $n+4$, and so on, so the system is not closed. Under genic selection ($h = 1/2$) only $\Phi_{n+1}$ appears.

**Jackknife closure.** Approximate the larger-sample spectra by sparse linear extrapolations of the current one, $\Phi_{n+1} \approx J_{n \to n+1}\Phi_n$ and $\Phi_{n+2} \approx J_{n \to n+2}\Phi_n$, where each entry of $J_{n\to n+k}\Phi_n$ is a fixed linear combination of three neighboring entries of $\Phi_n$ (a third-order jackknife). Substituting, and using the leading-order source $nu\,\delta_{i,1}$, gives the closed linear system

$$\dot\Phi_n = \frac{1}{4N}\tilde\Delta_n \Phi_n + s\,\hat\nabla_{h,n}\Phi_n + nu\, e_1, \qquad \hat\nabla_{h,n} = \tilde\nabla_{h,n} J_{n\to n+2},$$

which can be integrated forward in time; migration between populations, which also raises the sample size by one in the source population, is closed in the same way.

## Remarks

The selection term comes from one integration by parts of the transport term against $w_{n,i}$; since $w_{n,i}'\,x(1-x)(h + (1-2h)x)$ has degree $n+1$ or $n+2$, it is a combination of binomial weights of those larger sample sizes. The closure is justified by the observation that a sample of size $n+2$ carries little information beyond a sample of size $n$ when $n$ is large: the extrapolation error decreases with $n$, so accuracy can be increased by integrating at a larger $n'$ and projecting down to the target sample size by hypergeometric subsampling. Because the closed system acts on $\prod_j(n_j - 1)$ unknowns and involves only sparse operators, it handles up to five populations, whereas finite-difference solvers of the multi-dimensional diffusion equation become impractical beyond three.

## Depends on

- [Moment equations for the neutral sample frequency spectrum](moment-equations-for-the-neutral-sample-frequency-spectrum.md)

## Sources

- J. Jouganous, W. Long, A. P. Ragsdale and S. Gravel, "Inferring the joint demographic history of multiple populations: beyond the diffusion approximation", Genetics 206 (2017), 1549–1567, Equations (5)–(8), Appendix A (Equation (A3)), Appendix C (selection term) and Appendix D, <https://doi.org/10.1534/genetics.117.200493>, PMCID PMC5500150.
