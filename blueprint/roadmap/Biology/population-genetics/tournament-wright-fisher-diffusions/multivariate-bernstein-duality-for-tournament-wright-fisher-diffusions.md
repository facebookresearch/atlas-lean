# Multivariate Bernstein duality for tournament Wright–Fisher diffusions

**Setting.** Fix $d\ge2$ types and a tournament matrix $T$ ($T_{ii}=0$, $T_{ij}\in\{0,1\}$, $T_{ij}+T_{ji}=1$ for $i\ne j$; $T_{ij}=1$ means $i$ beats $j$), and put $A=T-T^{\mathsf T}$. In a population of $N$ individuals, competitions at rate $\lambda_N$ per ordered pair give the target the winner's type and neutral reproductions at rate $\gamma_N$ copy the source. Under diffusive scaling the type-frequency vector $\mathbf X$ on the simplex $\Delta_d$ solves the martingale problem for
$$\mathcal Lf(\mathbf x)=\lambda\sum_{j=1}^dx_j(A\mathbf x)_j\,\partial_jf(\mathbf x)+\frac\gamma2\sum_{i,j=1}^dx_i(\delta_{ij}-x_j)\,\partial_{ij}f(\mathbf x),\qquad\lambda,\gamma\ge0.$$

**Bernstein coefficients.** For $n\ge1$ let $\mathcal K_n=\{\mathbf k\in\mathbb N_0^d:|\mathbf k|=n\}$ and $\mathcal V_n$ the functions $v:\mathcal K_n\to\mathbb R$. The Bernstein evaluation is $H(v,\mathbf x)=\sum_{\mathbf k\in\mathcal K_n}v(\mathbf k)\binom{n}{\mathbf k}\mathbf x^{\mathbf k}=\mathbb E[v(\mathbf M_n(\mathbf x))]$, with $\mathbf M_n(\mathbf x)$ multinomial. With $w,\ell$ the tournament winner and loser of two types, define the selection operator $S_n:\mathcal V_n\to\mathcal V_{n+1}$, $(S_nv)(\mathbf k)=\mathbb E[v(\mathbf k-\mathbf e_{\ell(i_{U_1},i_{U_2})})]$ (two individuals sampled without replacement from a population with type counts $\mathbf k$, the loser removed), and the coalescent operator $C_n:\mathcal V_n\to\mathcal V_{n-1}$, $(C_nv)(\mathbf k)=\sum_j\frac{k_j}{n-1}v(\mathbf k+\mathbf e_j)$.

**Coefficient process.** $V$ is the pure-jump process on $\bigsqcup_n\mathcal V_n$ with generator $\mathcal BF(v)=\lambda n[F(S_nv)-F(v)]+\gamma\binom n2[F(C_nv)-F(v)]$ for $v\in\mathcal V_n$; its degree performs a birth–death chain $n\to n+1$ at rate $\lambda n$ and $n\to n-1$ at rate $\gamma\binom n2$, which does not explode.

**Theorem 2.4 (multivariate Bernstein duality).** For every continuous solution $\mathbf X$ of the martingale problem for $(\mathcal L,C^2(\Delta_d))$, every $t\ge0$, $n\in\mathbb N$, $v\in\mathcal V_n$ and $\mathbf x\in\Delta_d$,
$$\mathbb E_{\mathbf x}\big[H(v,\mathbf X_t)\big]=\mathbb E_v\big[H(V_t,\mathbf x)\big].$$

**Corollaries 4.1–4.2.** Taking $v=\delta_{\mathbf k}$ gives $\mathbb E_{\mathbf x}\big[\prod_jX_j(t)^{k_j}\big]=\binom{n}{\mathbf k}^{-1}\mathbb E_{\delta_{\mathbf k}}[H(V_t,\mathbf x)]$, so all mixed moments are determined, and the martingale problem for $\mathcal L$ is well posed with a Feller strong Markov solution.

## Depends on

- [Process-level selection duality with the ASG line-counting process](../diffusion-theory/selection-duality-and-general-one-dimensional-di/process-level-selection-duality-with-the-asg-lin.md)

## Expansion

The duality follows from two intertwining identities between the generators acting on $H(v,\mathbf x)$. Selection: $H(S_nv,\mathbf x)-H(v,\mathbf x)=\sum_i\sum_{j\ne i}x_ix_jA_{ij}\mathbb E[v(\mathbf M_{n-1}(\mathbf x)+\mathbf e_i)]$, which matches $\lambda n$ times the drift term (Proposition 3.5). Coalescence: $\frac\gamma2\sum_{i,j}x_i(\delta_{ij}-x_j)\partial_{ij}H(v,\mathbf x)=\gamma\binom n2[H(C_nv,\mathbf x)-H(v,\mathbf x)]$ (Proposition 3.7). Hence $\mathcal L_{\mathbf x}H(v,\mathbf x)=\mathcal B_vH(v,\mathbf x)$, and the standard duality argument, using nonexplosion of the degree chain, gives equality of the two semigroups. Backward in time, a selective event adds a potential parent line whose type is decided by the tournament, the multitype analogue of branching in the ancestral selection graph.

## Sources

- O. Angtuncio Hernández, "Multivariate Bernstein duality for tournament Wright--Fisher diffusions", arXiv preprint (2026), Definition of the coefficient process, Theorem 2.4, Propositions 3.5 and 3.7, Corollaries 4.1–4.2, <https://doi.org/10.48550/arXiv.2611.13731>.
