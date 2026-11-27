# Matrix-norm condition for epidemic containment along a trajectory

**Model.** A country is divided into $M$ regions with SIQHDR compartments $S_i,I_i,Q_i,H_i,D_i,R_i$ (susceptible, undetected infected, quarantined, hospitalized, deceased, recovered) evolving in discrete time (days). A fraction $\phi_{ij}(t)\in[0,1]$ of the people of region $i$ interacts in region $j$ during day $t$, $\rho_j(t)\in[0,1]$ is the social-distancing level in region $j$, and $N^{p}_j=\sum_k\phi_{kj}(S_k+I_k+R_k)$ is the free-to-move population present in $j$. The infected compartments obey

$$I_i(t+1)=I_i(t)+\beta S_i(t)\sum_{j=1}^{M}\frac{\rho_j(t)\phi_{ij}(t)}{N^{p}_j(t)}\sum_{k=1}^{M}\phi_{kj}(t)I_k(t)-(\gamma+\alpha_i(t)+\psi_i)I_i(t),$$

where $\gamma$ is recovery, $\alpha_i(t)$ detection by testing and $\psi_i$ hospitalization, with $\gamma+\alpha_i(t)+\psi_i\le1$. Compactly $I(t+1)=(\mathcal I+\Psi(x(t),u(t)))\,I(t)$ with

$$\Psi_{ij}=\beta S_i\sum_{k=1}^{M}\frac{\rho_k\phi_{ik}\phi_{jk}}{N^{p}_k}-(\alpha_i+\psi_i+\gamma)\,[i=j],$$

where $u=(\rho,\varphi,\sigma)\in[0,1]^{3M}$ collects distancing, travel-restriction and testing controls. Along a reference trajectory $(\bar x,\bar u)$, a perturbation of the infected only evolves as $\delta I(t+1)=(\mathcal I+\Psi+\Gamma)\,\delta I(t)$, where $\Gamma_{ij}=\sum_q\frac{\partial\Psi_{iq}}{\partial I_j}I_q\le0$ accounts for the dependence of $N^{p}$ on $I$.

**Proposition (containment).** Suppose that for some induced $\ell_q$ matrix norm and some $c<1$,

$$\big\|\mathcal I+\Psi(\bar x(t),\bar u(t))\big\|_q\le c\qquad\text{for all }t\ge t_0 .$$

Then (i) $\|\bar I(t)\|_q\le c^{\,t-t_0}\|\bar I(t_0)\|_q$ and (ii) $\|\delta I(t)\|_q\le c^{\,t-t_0}\|\delta I(t_0)\|_q$ for all $t\ge t_0$.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

Part (i) is submultiplicativity of the induced norm applied to the product of one-step matrices. For part (ii), $B_2=\mathcal I+\Psi$ is entrywise nonnegative because each region loses at most all of its infected in one day, $B_1=\mathcal I+\Psi+\Gamma\le B_2$ because $\Gamma\le0$, and $B_1\ge0$ because $\sum_q\phi_{qk}I_q/N^{p}_k\le1$; for nonnegative matrices $0\le B_1\le B_2$ implies $\|B_1\|_q\le\|B_2\|_q$, so the same contraction factor applies. With $q=1$, (i) says total infections decrease and (ii) says each infection generates on average fewer than one new infection along the trajectory, a time-varying network analogue of an effective reproduction number below one, for which no closed form is available in such models. With $q=\infty$, the largest regional variation of infected decreases, which also prevents amplification of bounded disturbances. The source imposes the condition as a constraint in a model predictive controller that schedules intermittent regional distancing, travel and testing measures for a three-region model of Italy, and shows it reduces to a known condition for network SIS models.

## Sources

- Marco Coraggio, Shihao Xie, Francesco De Lellis, Giovanni Russo, Mario Di Bernardo, "Intermittent non-pharmaceutical strategies to mitigate the COVID-19 epidemic in a network model of Italy via constrained optimization", in 2021 60th IEEE Conference on Decision and Control (CDC) (2021), 3538–3543, <https://doi.org/10.1109/cdc45484.2021.9683420>. Published version of arXiv:2103.16502, cited next; locators there refer to the arXiv version.
- M. Coraggio, S. Xie, F. De Lellis, G. Russo and M. di Bernardo, "Intermittent non-pharmaceutical strategies to mitigate the COVID-19 epidemic in a network model of Italy via constrained optimization", arXiv:2103.16502 (2021), Mathematical Preliminaries (Lemma 1), Section 2 (network SIQHDR model), Section 3 (Proposition 1 and its interpretation) and Section 4 (control problem), <https://doi.org/10.48550/arXiv.2103.16502>.
