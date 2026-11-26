# Transient Turing instability of the periodic chemotaxis–competition system

Let $\Omega\subset\mathbb{R}^n$ be a bounded smooth domain and let $f_1,f_2\in C^1([0,T])$ be $T$-periodic with $1+f_i(t)>0$ (seasonally varying carrying capacities). Two Lotka–Volterra competitors $u,v$ produce a chemical signal $w$ and respond chemotactically:

$$
\begin{aligned}
u_t&=\Delta u-\chi_1\nabla\cdot(u\nabla w)+\mu_1u\,(1+f_1(t)-u-a_1v),\\
v_t&=\Delta v-\chi_2\nabla\cdot(v\nabla w)+\mu_2v\,(1+f_2(t)-v-a_2u),\\
0&=\Delta w+\alpha u+\beta v-w,
\end{aligned}
$$

in $\Omega\times(0,\infty)$ with homogeneous Neumann conditions, where $\mu_i,\alpha,\beta>0$ and $a_i\ge0$. Let $(\tilde u(t),\tilde v(t))$ be a nonnegative, globally attracting $T$-periodic solution of the kinetic system $\tilde u'=\mu_1\tilde u(1+f_1-\tilde u-a_1\tilde v)$, $\tilde v'=\mu_2\tilde v(1+f_2-\tilde v-a_2\tilde u)$ (either periodic coexistence or periodic exclusion), and set $\tilde w=\alpha\tilde u+\beta\tilde v$.

**Theorem.** Assume in addition

$$
\alpha\left(1+f_2(t)\right)\le\alpha a_2\,\tilde u(t)+(2\alpha-a_2\beta)\,\tilde v(t)\qquad\text{for all }t\in[0,T].
$$

Then there is $\chi_{\mathrm{crit}}\in\mathbb{R}$ such that for every $\chi_1>\chi_{\mathrm{crit}}$ there is a nonempty set of times $\mathcal{I}\subset[0,T]$ over which the spatially homogeneous periodic state $(\tilde u,\tilde v,\tilde w)$ is linearly unstable: at each $t\in\mathcal{I}$ at least one Neumann Fourier mode of the linearised perturbation grows at an exponential rate. Because all coefficients are $T$-periodic, the instability recurs on $\mathcal{I}+kT$ for every $k\in\mathbb{N}_0$.

## Depends on

- [Diffusion-driven instability (Turing 1952)](../turing-patterns-and-diffusion-driven-instability/turing-instability.md)

## Expansion

Linearising about $(\tilde u,\tilde v,\tilde w)$ and expanding in Neumann eigenfunctions of $-\Delta$ with eigenvalues $\lambda_k$, the elliptic equation gives the signal mode as $(\alpha C_1^{(k)}+\beta C_2^{(k)})/(1+\lambda_k)$, leaving a $2\times2$ nonautonomous system $\dot C^{(k)}=A_k(t)C^{(k)}$ in which $\chi_1$ enters through the term $\chi_1\tilde u\,\lambda_k/(1+\lambda_k)$. Differentiating decouples it into second-order equations $y''+\mathcal P_k(t)y'+\mathcal Q_k(t)y=0$; whenever $\mathcal Q_k<0$ on an interval, every nonzero solution grows exponentially there (a comparison result for nonautonomous linear ODEs). The displayed inequality makes $\mathcal Q_k$ affine in $\chi_1$ with negative slope, so for each mode there is a threshold beyond which $\mathcal Q_k$ becomes negative on a set of times; $\chi_{\mathrm{crit}}$ is the infimum of these thresholds over modes. Unlike autonomous Turing instability, an unstable mode is amplified only during part of each period and decays in between, producing recurrent transient aggregation without a Hopf bifurcation; for small sensitivities the homogeneous periodic state is known to be globally attracting.

## Sources

- F. Herrero-Hervás, P. Hernández-Alonso, M. Negreanu, "Transient instability and recurrent aggregation in a two-species chemotaxis-competition system under environmental periodicity", Theorem 1.1, Lemma 3.1 and Section 3. <https://doi.org/10.48550/arXiv.2608.07701>
