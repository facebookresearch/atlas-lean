# Mean-square stability of explicit and nonstandard finite-difference schemes for a stochastic predator-prey diffusion

**Setting.** On a grid $x_j=jh$, $t_k=k\Delta\tau$, approximate the stochastic ratio-dependent predator-prey reaction-diffusion system

$$P_t=\sigma_1P_{xx}+P(a-bP)-\frac{cPQ}{mQ+P}+\eta_1P\dot B_1(t),\qquad Q_t=\sigma_2Q_{xx}-dQ+\frac{fPQ}{mQ+P}+\eta_2Q\dot B_2(t),$$

with independent standard Wiener processes $B_1,B_2$, bounded noise strengths $\eta_1,\eta_2$, homogeneous Neumann boundary conditions and positive initial data. Put $D_i=\sigma_i\Delta\tau/h^2$ and $\Delta B_i^k=B_i((k+1)\Delta\tau)-B_i(k\Delta\tau)$, so $\mathbb E(\Delta B_i^k)^2=\Delta\tau$.

- *Stochastic forward Euler (SFE):* $P^{k+1}_j=D_1(P^k_{j+1}+P^k_{j-1})+(1-2D_1)P^k_j+\Delta\tau\,P^k_j(a-bP^k_j)-\Delta\tau\,\frac{cP^k_jQ^k_j}{mQ^k_j+P^k_j}+\eta_1P^k_j\Delta B_1^k$, and analogously for $Q$.
- *Stochastic nonstandard finite differences (Mickens type):* the diagonal and loss terms move to the new time level,

$$P^{k+1}_j=\frac{D_1(P^k_{j+1}+P^k_{j-1})+(1+a\Delta\tau)P^k_j+\eta_1P^k_j\Delta B_1^k}{1+2D_1+b\Delta\tau P^k_j+c\Delta\tau\,Q^k_j/(mQ^k_j+P^k_j)},\quad Q^{k+1}_j=\frac{D_2(Q^k_{j+1}+Q^k_{j-1})+Q^k_j+f\Delta\tau\,\frac{P^k_jQ^k_j}{mQ^k_j+P^k_j}+\eta_2Q^k_j\Delta B_2^k}{1+2D_2+d\Delta\tau}.$$

The source's Eq. (14) prints the predator numerator without the term $Q^k_j$; the page restores it as the source's own consistency computation (26) and linearization (28) contain it. Without it, inserting a smooth solution leaves an $O(1)$ residual $Q(x_j,t_k)$ in the truncation error, and the predator scheme is not consistent.

**Statement (von Neumann analysis in mean square, linearized prey equation).** For a Fourier mode $e^{\iota j\theta}$, $\theta\in[-\pi,\pi]$, the amplification factors are

$$g_{\rm SFE}=1+a\Delta\tau-4D_1\sin^2\tfrac{\theta}{2}+\eta_1\Delta B_1,\qquad g_{\rm NSFD}=\frac{1+a\Delta\tau+2D_1-4D_1\sin^2\frac{\theta}{2}+\eta_1\Delta B_1}{1+2D_1}.$$

Hence

$$\mathbb E|g_{\rm NSFD}|^2=\Big(\frac{1+2D_1\cos\theta+a\Delta\tau}{1+2D_1}\Big)^2+\frac{\eta_1^2\Delta\tau}{(1+2D_1)^2}\le 1+K\Delta\tau$$

for every $D_1>0$ and $\Delta\tau\le\Delta\tau_0$, with $K$ depending on $a$, $\eta_1$ and $\Delta\tau_0$ (e.g. $K=2|a|+a^2\Delta\tau_0+\eta_1^2$): the nonstandard scheme is stable in mean square with no restriction linking $\Delta\tau$ and $h$. Without a bound on the step no such $K$ exists: at $\theta=0$ the deterministic factor is $(1+2D_1+a\Delta\tau)/(1+2D_1)\to1+a\Delta\tau$ as $D_1\to0$, and $(1+a\Delta\tau)^2>1+K\Delta\tau$ for large $\Delta\tau$ when $a>0$. The source's proof of Theorem 5 bounds this deterministic factor by $1$ and concludes $\mathbb E|g|^2\le1+|\eta_1|^2\Delta\tau$, which fails at $\theta=0$ when $a>0$; the page therefore states the bound with the constant above instead. The explicit scheme requires the deterministic part $|1+a\Delta\tau-4D_1\sin^2(\theta/2)|\le 1+O(\Delta\tau)$ for all $\theta$, which, at the mode $\theta=\pi$ of the source's Eq. (18), forces the parabolic restriction $D_1\le 1/2+O(\Delta\tau)$; the predator equation gives the same picture with $a$ replaced by $-d$. Both schemes are consistent with the system in mean square, $\mathbb E|L(\phi)-L_h(\phi)|^2\to0$ for smooth $\phi$ as $h,\Delta\tau\to0$.

## Expansion

Linearizing the prey update and inserting a single Fourier mode gives the factors above; independence of $\Delta B_1^k$ from the current state removes the cross term, so the noise contributes the additive $\eta_1^2\Delta\tau$ (divided by $(1+2D_1)^2$ in the implicit-denominator scheme). In the nonstandard scheme $|1+2D_1\cos\theta|\le1+2D_1$, so the deterministic factor has modulus at most $1+|a|\Delta\tau/(1+2D_1)\le1+|a|\Delta\tau$ whatever $D_1$ is; squaring and adding the noise term gives $\mathbb E|g|^2\le1+(2|a|+a^2\Delta\tau+\eta_1^2)\Delta\tau$, so the Lax-Richtmyer growth condition $|g|^2\le1+K\Delta\tau$ holds for $\Delta\tau\le\Delta\tau_0$ with no condition on $h$. In the explicit scheme the mode $\theta=\pi$ gives $1-4D_1+a\Delta\tau$, whose modulus exceeds one by an $O(1)$ amount once $D_1>1/2$. The nonstandard denominators are positive for positive data, which is the design reason (after Mickens) for preferring it for population densities; the source's simulations show the explicit scheme losing positivity and convergence at step sizes where the nonstandard one stays positive.

## Depends on

- [Coexistence equilibrium of the ratio-dependent predator-prey model](coexistence-equilibrium-of-the-ratio-dependent-predator-prey-model.md)

## Sources

- Yasin MW, Ahmed N, Iqbal MS, Raza A, Rafiq M, Eldin EMT, Khan I. Spatio-temporal numerical modeling of stochastic predator-prey model. *Scientific Reports* 13 (2023). <https://doi.org/10.1038/s41598-023-28324-6> (PMCID: PMC10439196). Schemes (11)-(14); Theorems 2-3 (mean-square consistency), Theorem 4 (conditional stability of the explicit scheme), Theorem 5 (stability of the nonstandard scheme).
