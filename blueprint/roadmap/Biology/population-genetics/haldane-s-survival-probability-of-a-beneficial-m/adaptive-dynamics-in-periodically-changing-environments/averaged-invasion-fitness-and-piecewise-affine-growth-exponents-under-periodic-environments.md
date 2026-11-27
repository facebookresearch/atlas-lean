# Averaged invasion fitness and piecewise affine growth exponents under periodic environments

**Model.** Traits are the vertices of a finite directed graph $G=(V,E)$ with graph distance $d(u,w)$. The environment cycles through $\ell$ phases; phase $i$ lasts $T_i\lambda_K$ time units, where

$$1\ll\lambda_K\ll\ln K,$$

and has constant birth, death and competition rates $b^i_v,d^i_v,c^i_{v,w}$; the time-dependent rates $b^K_v(t)$, etc. are the periodic extensions. The population $N^K\in\mathbb{N}_0^V$ is a Markov process with generator

$$\mathcal{L}^K_t\phi(N)=\sum_v[\phi(N+\delta_v)-\phi(N)]\Big(N_vb^K_v(t)(1-\mu_K)+\sum_wN_wb^K_w(t)\mu_Km_{w,v}\Big)+\sum_v[\phi(N-\delta_v)-\phi(N)]N_v\Big(d^K_v(t)+\sum_w\tfrac{c^K_{v,w}(t)}{K}N_w\Big),$$

with mutation kernel $m$ satisfying $m_{v,v}=0$ and $m_{v,w}>0$ if and only if $(v,w)\in E$, competition rates with $c^i_{v,v}>0$ for all $v$ and $i$ (Assumption 1 of the source), and mutation probability $\mu_K=K^{-1/\alpha}$, $\alpha\in(0,\infty)\setminus\mathbb{N}$.

**Fitness.** If trait $v$ alone has equilibrium $\bar n^i_v=(b^i_v-d^i_v)/c^i_{v,v}>0$ in phase $i$, the invasion fitness of $w$ against $v$ is $f^i_{w,v}=b^i_w-d^i_w-c^i_{w,v}\bar n^i_v$, and its time average is

$$f^{\mathrm{av}}_{w,v}=\frac{\sum_{i=1}^{\ell}T_if^i_{w,v}}{\sum_{i=1}^{\ell}T_i}.$$

**Statement.** Let $\beta^K_w(s)=\ln(N^K_w(s\ln K)+1)/\ln K$. Assume $\beta^K_w(0)\to\bar\beta_w(0)$ in probability, with $\bar\beta_w(0)=\max_u[\bar\beta_u(0)-d(u,w)/\alpha]\vee0$ and $\bar\beta_w(0)=1$ only for the initial resident $v_0$. Define invasion times $s_0=0$, $s_k=\inf\{t>s_{k-1}:\bar\beta_w(t)=1\text{ for some }w\neq v_{k-1}\}$ with $v_k$ that trait, and on $[s_{k-1},s_k]$

$$\bar\beta_w(t)=\max_{u\in V}\Big[\bar\beta_u(s_{k-1})+(t-t_{u,k})_+\,f^{\mathrm{av}}_{u,v_{k-1}}-\frac{d(u,w)}{\alpha}\Big]\vee 0,$$

where $t_{u,k}$ is the time trait $u$ first appears (a neighbour reaches exponent $1/\alpha$), up to a stopping time $T_0$ at which the construction ceases to be monomorphic or unambiguous. Then for every $T\le T_0$, $(\beta^K_w)_{w\in V}\to(\bar\beta_w)_{w\in V}$ in probability in $L^\infty([0,T])$. Moreover, there is $\varepsilon_0>0$ such that for every $\varepsilon\in(0,\varepsilon_0)$ and every $p\in[1,\infty)$, the point measure on traits of size above $\varepsilon K$ at time $s\ln K$ converges in $L^p([0,T])$ to $\sum_k\mathbf{1}_{[s_k,s_{k+1})}(s)\,\delta_{v_k}$: a substitution sequence of residents driven by averaged, not instantaneous, fitness.

## Expansion

Between environmental switches the resident has time $\lambda_K\gg1$ to relax to its new equilibrium (exponential concentration estimates for logistic birth-death processes), so mutants effectively see a piecewise constant resident and behave like birth-death(-immigration) processes with periodic rates. Since a full period has length of order $\lambda_K\ll\ln K$, the integrated growth rate over a time $s\ln K$ is $s\ln K\cdot f^{\mathrm{av}}+O(\lambda_K)$, so on the $\ln K$ scale a birth-death process started at $K^{\beta}$ has exponent $(\beta+r^{\mathrm{av}}s)\vee0$. Each trait also receives a $K^{-d(u,w)/\alpha}$ fraction of the population of every trait $u$ through chains of mutations, and the leading term gives the maximum formula. A mutant reaching exponent $1$ triggers an order-one Lotka-Volterra invasion, timed to occur in a phase with positive invasion fitness.

## Sources

- Manuel Esser and Anna Kraut, "Effective growth rates in a periodically changing environment: From mutation to invasion", Stoch. Process. Appl. 184 (2025), 104598, <https://doi.org/10.1016/j.spa.2025.104598>. Numbering follows the arXiv version, arXiv:2310.20509 (2023): Section 2 (generator, invasion fitness definition, Theorem 2.4 and Corollary 2.5), Theorem B.1, <https://doi.org/10.48550/arXiv.2310.20509>.
