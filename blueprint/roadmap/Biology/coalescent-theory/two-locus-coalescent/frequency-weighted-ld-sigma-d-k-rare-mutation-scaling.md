# Frequency-resolved linkage disequilibrium $\sigma_d^k(f_0)$ and its rare-mutation scaling collapse

Consider a haploid two-locus model with constant population size $N$, mutation rate $\mu$ per locus ($N\mu\ll1$, infinite sites), recombination rate $R$, and fitness costs $s_A$, $s_B$ of the single mutants and $s_{AB}=s_A+s_B+\epsilon$ of the double mutant (also semidominant diploids). With haplotype frequencies $f_{Ab},f_{aB},f_{AB}$, allele frequencies $f_A=f_{Ab}+f_{AB}$, $f_B=f_{aB}+f_{AB}$, and $D=f_{AB}-f_Af_B$, define for a frequency scale $f_0>0$ and $k\ge1$

$$\sigma_d^k(f_0)=\frac{\big\langle D^k\, e^{-(f_A+f_B)/f_0}\big\rangle}{\big\langle f_A(1-f_A)f_B(1-f_B)\, e^{-(f_A+f_B)/f_0}\big\rangle}.$$

As $f_0\to\infty$, $\sigma_d^2(f_0)$ is the Ohta-Kimura ratio $\sigma_d^2=\langle D^2\rangle/\langle f_A(1-f_A)f_B(1-f_B)\rangle$, whose neutral value is $(5+NR)/(11+13NR+2(NR)^2)$. Equivalently $\sigma_d^2(f_0)=\mathbb E[r^2\,W(f_A,f_B\mid f_0)]$ with weight $W\propto f_A(1-f_A)e^{-f_A/f_0}\,f_B(1-f_B)e^{-f_B/f_0}$ normalized to $\mathbb E[W]=1$.

**Rare-mutation limit.** For $f_0\ll1$ the mutant haplotypes follow the branching-process (Langevin) equations

$$\dot f_{Ab}=-s_Af_{Ab}+\mu+RD+\sqrt{f_{Ab}/N}\,\eta_{Ab},\quad \dot f_{aB}=-s_Bf_{aB}+\mu+RD+\sqrt{f_{aB}/N}\,\eta_{aB},$$

$$\dot f_{AB}=-s_{AB}f_{AB}-RD+\mu(f_{Ab}+f_{aB})+\sqrt{f_{AB}/N}\,\eta_{AB},$$

with independent unit white noises. In the scaled parameters

$$\theta=2N\mu,\quad \rho=2NRf_0,\quad \gamma_i=2Ns_if_0\ (i=A,B,\epsilon),$$

and to leading order in $\theta$ and $f_0$:

1. The weighted single-locus law is the frequency spectrum of a deleterious mutation with $\gamma^*=\gamma+1$: $p(f\mid f_0)\approx 2N\mu\, e^{-2Nsf-f/f_0}/f$, so $\langle f_Af_B\,e^{-(f_A+f_B)/f_0}\rangle\approx\theta^2f_0^2/[(1+\gamma_A)(1+\gamma_B)]$.
2. **Scaling collapse:** $\sigma_d^k(f_0)\,f_0^{1-k}\approx\Sigma_d^k(\gamma_A,\gamma_B,\gamma_\epsilon,\rho)$, a dimensionless function independent of $\mu$, given by

$$\Sigma_d^k=-\delta_{k,1}+(1+\gamma_A)(1+\gamma_B)\int_0^\infty\psi_k(\tau)\big[\Phi_A(\tau)+\Phi_B(\tau)+\rho\,\Phi_A(\tau)\Phi_B(\tau)\big]\,d\tau,$$

where $\Phi_A(\tau)=(\gamma_A+1-e^{-\gamma_A\tau})/[\gamma_A(\gamma_A+1)]$, $\Phi_B$ likewise, and $\psi_k=(-1)^{k+1}\partial_z^k\psi|_{x=y=1,z=2}$ for the solution $\psi(x,y,z,\tau)$ of the characteristic equation

$$\partial_\tau\psi=-\gamma_{AB}\psi-\psi^2+\frac{\rho\gamma_Ax\,e^{-\gamma_A\tau}}{\gamma_A+x(1-e^{-\gamma_A\tau})}+\frac{\rho\gamma_By\,e^{-\gamma_B\tau}}{\gamma_B+y(1-e^{-\gamma_B\tau})},\qquad \psi(\cdot,0)=z,$$

with $\gamma_{AB}=\gamma_A+\gamma_B+\gamma_\epsilon+\rho$.

Consequently parameter sets with equal $(\gamma_A,\gamma_B,\gamma_\epsilon,\rho)$ give the same $\sigma_d^k f_0^{1-k}$: for neutral loci a change of $R$ is equivalent to a change of $f_0$ with $NRf_0$ fixed. For $\rho=0$ the characteristic equation is solved by $\psi=\gamma_{AB}z\,e^{-\gamma_{AB}\tau}/[\gamma_{AB}+z(1-e^{-\gamma_{AB}\tau})]$, reducing $\Sigma_d^2$ to a one-dimensional integral.

## Depends on

- [Stationary standardized linkage disequilibrium $\sigma_d^2$](sigma-dsq.md)
- [Ohta–Kimura standardized disequilibrium $\sigma_d^2$](sigma-dsq-eq.md)

## Proof depends on

- [Ohta–Kimura standardized disequilibrium $\sigma_d^2$](sigma-dsq-eq.md)
- [Stationary standardized linkage disequilibrium $\sigma_d^2$](sigma-dsq.md)

## Expansion

The exponential weight is chosen because it turns weighted moments into derivatives of the generating function $H(x,y,z,t)=\langle e^{-(xf_{Ab}+yf_{aB}+zf_{AB})/f_0}\rangle$ evaluated at $(x,y,z)=(1,1,2)$; the shift by $2$ in $z$ reflects that $f_{AB}$ enters both $f_A$ and $f_B$. Applying Ito's formula to the linearized dynamics gives a first-order PDE for $H$. A perturbation series $H=1+\sum\theta^if_0^jH_{ij}$ gives the product of single-locus generating functions $\log[1+x(1-e^{-\gamma_A\tau})/\gamma_A]$ at order $\theta$. At order $\theta^2f_0$ the linkage terms solve along the characteristic curve $\psi$. The weight removes the divergence of the neutral branching process, which is why the neutral spectrum looks deleterious with $\gamma^*=1$. Since $D^k$ is dominated by $f_{AB}^k$ at frequency scale $f_0$, the numerator is of order $\theta^2f_0^{k+1}$ and the denominator of order $\theta^2f_0^2$, hence the power $f_0^{k-1}$.

## Sources

- B. H. Good, "Linkage disequilibrium between rare mutations", Genetics 220(4) (2022), iyac004, <https://doi.org/10.1093/genetics/iyac004>, PMCID PMC8982034. Equations (2), (4)-(8) (statistics and rare-mutation dynamics), (47)-(51) (generating function and scaled parameters), (53)-(55) (weighted single-locus law), (56)-(60) (characteristic curve and scaling function), (61)-(62) (nonrecombining case).
