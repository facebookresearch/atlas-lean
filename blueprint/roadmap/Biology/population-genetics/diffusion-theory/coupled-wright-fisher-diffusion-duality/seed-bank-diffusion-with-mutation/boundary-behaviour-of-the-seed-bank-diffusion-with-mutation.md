# Boundary behaviour of the seed bank diffusion with mutation

**Model.** In the Wright–Fisher model with a strong (geometric) seed bank, $N$ active and $N/K$ dormant individuals exchange $c$ individuals per generation. Under diffusive scaling the frequencies $X$ (active) and $Y$ (dormant) of one allele converge to the *seed bank diffusion*. Adding two-way mutation at rates $u_1$ (away from the allele) and $u_2$ (towards it) in the active population and $u_1',u_2'$ in the seed bank gives

$$
\begin{aligned}
dX_t&=\big[-u_1X_t+u_2(1-X_t)+c(Y_t-X_t)\big]dt+\sqrt{X_t(1-X_t)}\,dB_t,\\
dY_t&=\big[-u_1'Y_t+u_2'(1-Y_t)+cK(X_t-Y_t)\big]dt,
\end{aligned}
$$

with $u_1,u_2,u_1',u_2'\ge0$, $c,K>0$ and $(X_0,Y_0)\in[0,1]^2$; this system has a unique strong solution.

**Theorem.** Started from the interior of $[0,1]^2$:

1. $X$ never hits $0$ if and only if $2u_2\ge1$;
2. $X$ never hits $1$ if and only if $2u_1\ge1$;
3. $Y$ never hits $0$;
4. $Y$ never hits $1$.

Without mutation ($u_i=u_i'=0$) the process is moment dual to the block-counting process $(N_t,M_t)$ of the seed bank coalescent, $\mathbb E_{x,y}[X_t^nY_t^m]=\mathbb E^{n,m}[x^{N_t}y^{M_t}]$, and converges to fixation with

$$
\mathcal L_{(x,y)}(X_\infty,Y_\infty)=\frac{y+xK}{1+K}\,\delta_{(1,1)}+\frac{1+(1-x)K-y}{1+K}\,\delta_{(0,0)} .
$$

## Depends on

- [Wright–Fisher diffusion with a strong seed bank](../../../../coalescent-theory/structured-coalescent/seed-bank-coalescent/wright-fisher-diffusion-with-a-strong-seed-bank.md)
- [Seed-bank coalescent](../../../../coalescent-theory/structured-coalescent/seed-bank-coalescent/seed-bank-coalescent-active-dormant-lineages.md)

## Expansion

The active coordinate behaves near its boundaries like a one-dimensional Wright–Fisher diffusion with mutation, whose boundary $0$ is inaccessible exactly when $2u_2\ge1$ (Feller's classification); the seed bank only adds a bounded drift $c(Y-X)$, which at $X=0$ points inward and does not change the critical mutation threshold. The dormant coordinate has no noise, and its drift at $Y=0$ is $u_2'+cKX\ge0$, strictly positive whenever $X>0$, so it cannot reach the boundary from the interior. The fixation law follows from duality: $(N_t,M_t)$ is absorbed in a single block that is active with probability $K/(1+K)$ and dormant with probability $1/(1+K)$ in stationarity, so $P(\text{fixation})=\frac{K}{1+K}x+\frac1{1+K}y$. The proof of the boundary theorem uses polynomial-diffusion theory and a McKean-type submartingale argument, and extends to two-island diffusions.

## Sources

- Jochen Blath, Noemi Kurt, "Population genetic models of dormancy", in *Probabilistic Structures in Evolution* (E. Baake and A. Wakolbinger, eds.), EMS Series of Congress Reports, EMS Press (2021), 247–266, <https://doi.org/10.4171/ECR/17-1/12>; preprint arXiv:2012.00810 (2020), section "Seed banks with spontaneous switching": Wright–Fisher model with strong seed bank, seed bank diffusion and its moment duality, fixation law, seed bank diffusion with mutation and Theorem 0.2.10 (the boundary theorem for positive rates, with strict thresholds), <https://doi.org/10.48550/arXiv.2012.00810>.
- J. Blath, E. Buzzoni, A. González Casanova and M. Wilke-Berenguer, "Structural properties of the seed bank and the two island diffusion", *Journal of Mathematical Biology* 79 (2019), 369–392, Theorem 3.1 (the boundary theorem as stated here, with $2u_2\ge1$, $2u_1\ge1$ and nonnegative rates), <https://doi.org/10.1007/s00285-019-01360-5>.
