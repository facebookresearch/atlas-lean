# Equilibria and threshold stability of the delayed media SVIRS model

**Model.** Susceptible $S$, vaccinated $V$, infected $I$ and recovered $R$ individuals evolve as
$$\begin{aligned}
S'&=\Lambda-\iota I\,e^{-mI(t-\tau)}S-(d_0+\varpi)S+\upsilon V+\vartheta R,\\
V'&=\varpi S-\sigma_0\iota I\,e^{-mI(t-\tau)}V-(d_0+\upsilon)V,\\
I'&=\iota I\,e^{-mI(t-\tau)}\big(S+\sigma_0V\big)-(d_0+\gamma_0+d)I,\\
R'&=\frac{\gamma_0 I}{1+\alpha I}-(d_0+\vartheta)R,
\end{aligned}$$
with all parameters positive and $\sigma_0\in[0,1]$: recruitment $\Lambda$, transmission $\iota$, media intensity $m$ acting with information delay $\tau\ge 0$, vaccination rate $\varpi$, relative susceptibility $\sigma_0$ of vaccinees, vaccine waning $\upsilon$, immunity waning $\vartheta$, natural and disease death $d_0,d$, recovery $\gamma_0$ saturated by limited treatment capacity $\alpha$. Initial histories lie in $C([-\tau,0],\mathbb R_+^4)$.

**Results.**
1. Positive initial data give positive solutions, and $N=S+V+I+R$ satisfies $N'\le\Lambda-d_0N$, so $\Omega=\{N\le\Lambda/d_0\}$ is positively invariant and attracting.
2. The unique disease-free equilibrium is $E^0=(S^0,V^0,0,0)$ with $S^0=\dfrac{\Lambda(d_0+\upsilon)}{d_0(d_0+\varpi+\upsilon)}$ and $V^0=\dfrac{\varpi\Lambda}{d_0(d_0+\varpi+\upsilon)}$, and
$$\mathcal R_0=\iota\,\frac{S^0+\sigma_0V^0}{d_0+\gamma_0+d}=\frac{\Lambda\iota\,(d_0+\upsilon+\sigma_0\varpi)}{d_0(d_0+\varpi+\upsilon)(d_0+\gamma_0+d)} .$$
3. If $\mathcal R_0>1$ and the media intensity is large enough,
$$m\ge\frac{\sigma_0\iota\varpi(1-\sigma_0)}{(d_0+\upsilon+\varpi)(d_0+\upsilon+\sigma_0\varpi)},$$
there is a unique endemic equilibrium $E^\ast=(S^\ast,V^\ast,I^\ast,R^\ast)$.
4. $E^0$ is locally asymptotically stable for $\mathcal R_0<1$ and unstable for $\mathcal R_0>1$, for every delay.
5. If $\iota\Lambda<d_0(d_0+\gamma_0+d)$, then $E^0$ is globally asymptotically stable in $\Omega$. This condition implies $\mathcal R_0<1$ because $S^0+\sigma_0V^0\le\Lambda/d_0$.
6. Under the conditions of item 3 the disease is uniformly persistent, and in the undelayed case $\tau=0$, under an additional parameter condition (P), $E^\ast$ is globally asymptotically stable for initial data with $I(0)>0$.

## Expansion

At $E^0$ the characteristic equation factors as $(\lambda+d_0+\vartheta)(\lambda+d_0)(\lambda+d_0+\upsilon+\varpi)\big(\lambda+d_0+\gamma_0+d-\iota(S^0+\sigma_0V^0)\big)=0$; the media factor $e^{-mI(t-\tau)}$ equals $1$ to first order at $I=0$, so the delay does not enter and the last root has the sign of $\mathcal R_0-1$. Eliminating $S^\ast,V^\ast,R^\ast$ reduces the endemic equilibrium to a scalar equation in $I^\ast$; the lower bound on $m$ is what makes its positive root unique. The global result for $E^\ast$ combines uniform persistence with the geometric (volume-contraction) criterion of Li and Muldowney, applied through the third additive compound of the four-dimensional Jacobian.

## Sources

- Songbo Hou and Xinxin Tian, "Stability and Hopf Bifurcation of a Delayed SVIRS Epidemic Model with Media Coverage", arXiv:2608.22303 (2026), Theorems 2.1–2.4, 3.1, 4.1, 4.2 and 4.3, <https://doi.org/10.48550/arXiv.2608.22303>.
