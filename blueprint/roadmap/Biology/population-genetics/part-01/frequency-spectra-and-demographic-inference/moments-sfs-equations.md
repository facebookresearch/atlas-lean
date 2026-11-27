# Moment equations for site-frequency spectra (moments)

Jouganous, Long, Ragsdale and Gravel (2017) evolve the expected site-frequency spectrum $\Phi_n$ of a sample of $n$ haploid copies directly. Drawing the $n$ sampled copies of the next generation from $n$ parental copies, with at most one coalescence among them per generation, gives a one-generation update $\Phi_n^{k+1}(i) = \Phi_n^k(i) + \frac{1}{4N}\tilde\Delta_{n,i}\Phi_n^k + U_i\Phi_n^k$ with a sparse linear drift operator $\tilde\Delta_{n,i}$ and a mutation operator $U_i$ (their Equation 2). Under the infinite-sites model the mutation term is the source $nu\,\delta_{i=1}$, giving the closed linear recursion $\Phi_n^{k+1}(i) = \Phi_n^k(i) + \frac{1}{4N}\tilde\Delta_{n,i}\Phi_n^k + nu\,\delta_{i=1}$ (Equation 3), which avoids both the diffusion approximation and the discretization of a partial differential equation. Approximating $\Phi_n^{k+1} - \Phi_n^k$ by a time derivative gives the continuous-time neutral system of ordinary differential equations $\dot\Phi_n(i) = \frac{1}{4N}\tilde\Delta_{n,i}\Phi_n + nu\,\delta_{i=1}$ (Equation 4). With selection (genotype acceptance probabilities $1$, $1 + hs$, $1 + s$ with selection coefficient $s \le 0$, and $ns \ll 1$), the update of $\Phi_n$ involves $\Phi_{n+2}$, which in turn involves $\Phi_{n+4}$, so the system is not closed (Equation 5); under genic selection ($h = 1/2$) only $\Phi_{n+1}$ enters (Appendix A). The closure replaces $\Phi_{n+2}$ by a third-order jackknife extrapolation $J_{n \to n+2}\Phi_n$, giving an approximate closed linear system (Equation 6). With several populations, migration couples spectra whose sample sizes differ by moving one copy between populations; for weak migration ($n_k m_{jk} \ll 1$) a jackknife from $n$ to $n + e_j$ again gives a closed approximate system (Equation 8).

## Expansion

1. The one-generation drift update of the sample spectrum, with at most one coalescence among the $n$ sampled copies, and the infinite-sites mutation source (Equations 2–3).
2. The neutral recursion (Equation 3), which avoids the diffusion and PDE-discretization approximations, and its continuous-time version (Equation 4).
3. The selection model, the dependence on $\Phi_{n+2}$ (on $\Phi_{n+1}$ when $h = 1/2$), and the jackknife closure (Equations 5–6) as an approximation.
4. The downsampling identity $\Phi_{n+1}(i+1) = \frac{i+2}{n+2}\Phi_{n+2}(i+2) + \frac{n-i+1}{n+2}\Phi_{n+2}(i+1)$ used in Appendix A.
5. The multi-population system with migration (Equation 7) and its weak-migration jackknife approximation (Equation 8).

## Sources

- J. Jouganous, W. Long, A. P. Ragsdale and S. Gravel, Inferring the joint demographic history of multiple populations: beyond the diffusion approximation, Genetics 206 (2017), 1549–1567, Model (Equations 2–8) and Appendix A. <https://doi.org/10.1534/genetics.117.200493>
