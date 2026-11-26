# Global extinction of both strains below the modified carrying capacity threshold

Two strains circulate in a host population with logistic births. $S$ are susceptibles, $I_1,I_2$ singly infected, $I_{12}$ coinfected, $R$ recovered with complete cross-immunity, and $N=S+I_1+I_2+I_{12}+R$:

$$
\begin{aligned}
S'&=\Big(b(1-\tfrac NK)-\alpha_1I_1-\alpha_2I_2-(\beta_1+\beta_2+\alpha_3)I_{12}-\mu_0\Big)S,\\
I_1'&=\Big(b(1-\tfrac NK)+\alpha_1S-\eta_1I_{12}-\gamma_1I_2-\mu_1\Big)I_1+\beta_1SI_{12},\\
I_2'&=\Big(b(1-\tfrac NK)+\alpha_2S-\eta_2I_{12}-\gamma_2I_1-\mu_2\Big)I_2+\beta_2SI_{12},\\
I_{12}'&=\Big(b(1-\tfrac NK)+\alpha_3S+\eta_1I_1+\eta_2I_2-\mu_3\Big)I_{12}+(\gamma_1+\gamma_2)I_1I_2,\\
R'&=\Big(b(1-\tfrac NK)-\mu_4'\Big)R+\rho_1I_1+\rho_2I_2+\rho_3I_{12}.
\end{aligned}
$$

All classes reproduce at rate $b$ with carrying capacity $K$. The $\alpha_k$ are transmission rates, $\beta_i$ single-strain transmission from coinfecteds, $\gamma_i,\eta_i$ superinfection rates, $\rho_i$ recovery rates, $\mu_i'$ class death rates, and $\mu_i=\rho_i+\mu_i'$. Assume $b>\mu_j$ for all $j$, and $\mu_0<\mu_4'<\mu_j'$ for $j=1,2,3$. Let

$$
S^{**}=\frac Kb(b-\mu_0)
$$

be the modified carrying capacity of a disease-free population, with $\hat\alpha_3=\alpha_3+\beta_1+\beta_2$.

1. **Bounds.** $\limsup_{t\to\infty}S(t)\le S^{**}$ and $\limsup_{t\to\infty}N(t)\le S^{**}$, while $\liminf_{t\to\infty}N(t)\ge\frac Kb(b-\mu_3')$.
2. **Global extinction.** If

$$
S^{**}<\min\Big\{\frac{\mu_1'-\mu_0}{\alpha_1},\ \frac{\mu_2'-\mu_0}{\alpha_2},\ \frac{\mu_3'-\mu_0}{\hat\alpha_3}\Big\},
$$

then the disease-free equilibrium $G_2=(S^{**},0,0,0,0)$ is globally asymptotically stable: $I_1,I_2,I_{12},R\to0$ and $S\to S^{**}$.

The strain invasion thresholds $\sigma_k=(\mu_k-\mu_0)/\alpha_k$ are compared with $S^{**}$, so increasing the carrying capacity $K$ moves the system through a succession of equilibria. At the single-strain equilibria the recovered population satisfies $0<K\,dR/dK<\sigma_k+R$, so $R$ grows with $K$ but is not uniformly bounded in $K$.

## Expansion

Summing the equations gives $N'\le(b(1-N/K)-\mu_0)N$, because every class dies at least at rate $\mu_0$. Comparison with the logistic equation gives the upper bounds, and the lower bound follows the same way using the largest death rate. Under the threshold inequality, eventually $\alpha_kS<\mu_k'-\mu_0$, so each infected class has a negative per-capita growth rate once $b(1-N/K)$ is close to $\mu_0$. A Lyapunov or comparison argument then drives the infected classes, and with them $R$, to zero.

## Sources

- S. Ghersheen, V. Kozlov and U. Wennergren, "Specifics of coinfection and its dynamics", arXiv:2110.14386 (2021), system (Model), assumption (assum2), Propositions 3.1–3.2, 5.1–5.2 and 7.1. <https://doi.org/10.48550/arXiv.2110.14386>
