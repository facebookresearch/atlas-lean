# Global stability of the polymorphic host-state equilibrium

**Setting.** In the limit of many hosts and large within-host parasite populations with balancing selection towards $\eta\in(0,1)$ and reinfection intensity $r>0$, the proportions $(v^0,v^\eta,v^1)$ of hosts that are pure type $B$, mixed (balanced at $\eta$) and pure type $A$ solve

$$\begin{aligned} \dot v^0&=(1-\eta)v^\eta-2r\eta\,v^0\big(v^1+\eta v^\eta\big),\\ \dot v^\eta&=-v^\eta+2r\big(\eta^2v^0v^\eta+(1-\eta)^2v^1v^\eta+v^0v^1\big),\\ \dot v^1&=\eta v^\eta-2r(1-\eta)\,v^1\big(v^0+(1-\eta)v^\eta\big) \end{aligned}$$

on the simplex $\Delta^3$. Let $r^\ast(\eta)=\max\Big\{\dfrac{2\eta-1}{2\eta(1-\eta)^2},\ \dfrac{1-2\eta}{2(1-\eta)\eta^2}\Big\}$.

**Proposition (equilibria).** Besides the monomorphic equilibria $(1,0,0)$ and $(0,0,1)$ there is an equilibrium $\mathbf u=(u^0,u^\eta,u^1)$ with

$$u^0=\frac{2r\eta(1-\eta)^2-(2\eta-1)}{2r\eta^2+4r^2\eta^3(1-\eta)},\qquad u^1=\frac{2r(1-\eta)\eta^2+2\eta-1}{2r(1-\eta)^2+4r^2\eta(1-\eta)^3},$$

and $u^\eta=1-u^0-u^1$; $\mathbf u\in\Delta^3$ iff $r\ge r^\ast(\eta)$. If $r>r^\ast(\eta)$, both monomorphic equilibria are saddles and $\mathbf u$ is globally stable on $\Delta^3\setminus\{(1,0,0),(0,0,1)\}$. If $r\le r^\ast(\eta)$, the monomorphic equilibrium of the type favoured at balance (type $A$ if $\eta>1/2$) is globally stable on the simplex minus the other vertex.

**Theorem (maintenance of diversity).** Consider $M_N$ hosts, each carrying $N$ parasites whose type-$A$ frequency moves in steps of $1/N$, with parasite reproduction at rate $g_N$ relative to host replacement. Assume there are $b\in(0,1)$, $r>0$ and $\epsilon>0$ with moderate selection $s_N=N^{-b}$, frequent reinfection $r_Ns_N\to r$, and fast parasite reproduction $1/g_N=o(N^{-3b-\epsilon})$ and $g_N=O\big(\exp(N^{1-b(1+\epsilon)})\big)$. Assume further $r>\max\Big\{\dfrac{\eta}{2(1-\eta)^2},\ \dfrac{1-\eta}{2\eta^2}\Big\}$ (a stronger condition than $r>r^\ast(\eta)$; for $\eta=1/2$ it reads $r>1$ while $r^\ast(1/2)=0$). Let parasites mutate between the two types at rate $u_N$ per parasite generation, so that the population mutation rate on the host time scale is $\theta_N:=u_N N M_N g_N$, and assume $\theta_N=o(r_N)$. Write $U^{\eta,N}\downarrow\{\eta\}$ for the shrinking neighbourhoods of $\eta$ that define the mixed host state, $W^{\delta,\mathbf u}$ for the open box of half-width $\delta$ around $\mathbf u$ in each coordinate, and $\tau^N_0$ for the first time all hosts are pure type $A$ or all are pure type $B$. Fix $\gamma>0$. Then there is a constant $c_1=c_1(\eta,r)$, independent of $N$, such that:

- for every $\delta>0$, started from a monomorphic host population (all hosts pure $A$, or all pure $B$), the host-state proportions enter $W^{\delta,\mathbf u}$ before time $\frac1{c_1\theta_Ns_N}+M_N^\gamma$ with probability tending to $1$;
- for every $\delta<\frac12\min\{u^0,u^\eta,u^1\}$, started with host-state proportions in $W^{\delta,\mathbf u}$ and with the fraction of hosts in states $\{0,1\}\cup U^{\eta,N}$ tending to $1$, the time $\tau^N_0$ until polymorphism is lost exceeds $\exp(M_N^{1-\gamma})$ with probability tending to $1$.

## Expansion

Mixed hosts are created when a pure host is successfully reinfected by the other type (rate proportional to $2r$ times the product of frequencies) and destroyed by host replacement (rate $1$), giving the quadratic–linear structure. At the all-$B$ vertex $(1,0,0)$, eliminating $v^0=1-v^\eta-v^1$ gives the Jacobian $\begin{pmatrix}-1+2r\eta^2&2r\\ \eta&-2r(1-\eta)\end{pmatrix}$ in $(v^\eta,v^1)$, with determinant $2r\big[(1-2\eta)-2r\eta^2(1-\eta)\big]$, negative (a saddle) exactly when $r>\frac{1-2\eta}{2(1-\eta)\eta^2}$; the all-$A$ vertex is symmetric under $\eta\leftrightarrow1-\eta$. These are the same conditions under which the numerators of $u^1$ and $u^0$ are positive, so the interior equilibrium enters the simplex exactly when both vertices become saddles. Once the deterministic system has a globally attracting interior point, large-deviation estimates for the $M_N$-host system give exponentially long persistence of both parasite types, matching the observed long-term coexistence of strains in persistent viral infections.

## Depends on

- [Host-state dynamics of a two-type parasite under balancing selection and reinfection](host-state-dynamics-of-a-two-type-parasite-under-balancing-selection-and-reinfection.md)

## Sources

- Cornelia Pokalyuk and Anton Wakolbinger, "Maintenance of diversity in a hierarchical host–parasite model with balancing selection and reinfection", *Stochastic Process. Appl.* 130(2) (2020), 1119–1158. <https://doi.org/10.1016/j.spa.2019.04.009>
- Preprint version (the locators in this item follow its numbering): Cornelia Pokalyuk, Anton Wakolbinger, "Maintenance of diversity in a hierarchical host-parasite model with balancing selection and reinfection", arXiv:1802.02429: Proposition 2.11 (equilibria and stability), Theorem 3 (maintenance of a polymorphic state), Proposition 3.13 (convergence to a neighbourhood of $\mathbf u$). <https://doi.org/10.48550/arXiv.1802.02429>
