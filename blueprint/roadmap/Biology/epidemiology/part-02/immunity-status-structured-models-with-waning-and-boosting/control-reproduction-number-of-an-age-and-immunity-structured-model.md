# Control reproduction number of an age- and immunity-structured model

**Model.** Split the population into age groups $n=1,\dots,N$ (aging rates $\tau_n$, with $\tau_N=0$; death rates $\mu_n$; fertilities $f_n$; per-capita contact rates $A_n$) and immune classes $i=1,\dots,5$: naive, some immunity, moderate immunity, recently vaccinated, fully immune. Susceptibles $S_{in}$ ($i\le5$) and infecteds $I_{jn}$ ($j\le4$) satisfy

$$\begin{aligned}
S_{in}'&=\tau_{n-1}S_{i,n-1}-(\tau_n+\mu_n+\Lambda_{in}+\omega_{in}+\rho_{in})S_{in}+\omega_{i+1,n}S_{i+1,n}+[\text{primary vaccination into } i=4],\\
S_{5n}'&=\tau_{n-1}S_{5,n-1}-(\tau_n+\mu_n+\omega_{5n})S_{5n}+\textstyle\sum_{j=1}^4\gamma_{jn}I_{jn}+\sum_{j=2}^4\rho_{jn}S_{jn},\\
I_{jn}'&=\tau_{n-1}I_{j,n-1}-(\tau_n+\mu_n+\gamma_{jn})I_{jn}+\Lambda_{jn}S_{jn},
\end{aligned}$$

where immunity wanes $i+1\to i$ at rates $\omega_{i+1,n}$ ($\omega_{1n}=0$), primary vaccination moves $S_{1n}\to S_{4n}$ at rate $\rho_{1n}$, boosters move $S_{jn}\to S_{5n}$ at rates $\rho_{jn}$, recovery leads to full immunity, births enter $S_{11}$, and the $n=1$ equations have no aging inflow. Under proportionate mixing the force of infection on class $(i,k)$ is $\Lambda_{ik}=\alpha_{ik}A_k\lambda(t)$ with susceptibility $\alpha_{ik}$ and

$$\lambda(t)=\frac{\sum_{j=1}^4\sum_{m=1}^NA_m\beta_{jm}I_{jm}(t)}{\sum_{m=1}^NA_mP_m},$$

where $\beta_{jm}$ is the infectivity of $I_{jm}$ and $P_m$ the size of age group $m$.

**Theorem.** Let $\tilde T_{jm}$ and $\tilde P_m$ be the sizes of class $(j,m)$ and age group $m$ at the disease-free equilibrium, and set

$$d_{jm}=\frac{1}{\tau_m+\mu_m+\gamma_{jm}},\qquad \pi_{jm}=\tau_md_{jm},\qquad \tilde c_{jm}=\frac{A_m\tilde T_{jm}}{\sum_{r=1}^NA_r\tilde P_r}.$$

Then the control reproduction number is

$$\mathcal R_v=\sum_{j=1}^{4}\sum_{k=1}^{N}\sum_{m=k}^{N}\alpha_{jk}A_k\,\tilde c_{jm}\,\beta_{jm}\,d_{jm}\Big(\prod_{s=k}^{m-1}\pi_{js}\Big)\frac{\tilde T_{jk}}{\tilde T_{jm}} .$$

Without vaccination ($\rho_{in}\equiv0$) only the naive class is populated at the disease-free equilibrium, and $\mathcal R_v$ reduces to the basic reproduction number $\mathcal R_0$, the same sum restricted to $j=1$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

An individual infected in class $(j,k)$ stays infectious in age group $m\ge k$ for mean time $d_{jm}$ and survives, still infectious, from group $s$ to $s+1$ with probability $\pi_{js}$. While in $(j,m)$ it infects members of $(j,k)$ at rate $\alpha_{jk}A_k\beta_{jm}\tilde c_{jm}/\tilde T_{jm}$ per susceptible, and there are $\tilde T_{jk}$ of them; summing over ages $m\ge k$, entry classes $(j,k)$ and immune classes gives $\mathcal R_v$. Formally, solving $I_{jm}=d_{jm}(\Lambda_{jm}S_{jm}+\tau_{m-1}I_{j,m-1})$ recursively gives $I_{jm}=Q_{jm}\lambda$, and substituting into the definition of $\lambda$ and dividing by $\lambda$ gives the endemic threshold $1=\sum A_m\beta_{jm}Q_{jm}/\sum A_rT_{jr}$; evaluating at the disease-free equilibrium gives the formula, which is confirmed as the dominant eigenvalue of the next-generation matrix.

## Sources

- R. M. Carlsson, L. M. Childs, Z. Feng, J. W. Glasser, J. M. Heffernan, J. Li, G. Röst, "Modeling the waning and boosting of immunity from infection or vaccination", Journal of Theoretical Biology (2020), Section 2.1 (Eqs. (2)–(7)), Section 2.2 (Eq. (8)), Section 3.2 (Eqs. (10)–(15), Theorem 1) and Appendix B (Eq. (B.1)), <https://doi.org/10.1016/j.jtbi.2020.110265>, PMCID PMC9108945.
