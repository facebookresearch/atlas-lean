# Poisson sampling formulas for McDonald–Kreitman tables of two diverged species

**Setting.** Two daughter species split from a common ancestor at scaled time $t$ in the past, with equal effective sizes, scaled mutation rates $\theta_s$ (silent) and $\theta_r$ (replacement), and scaled selection coefficient $\gamma$ for replacement mutations (silent ones neutral). Write $\beta_s=(t,\theta_s,0)$ and $\beta_r=(t,\theta_r,\gamma)$. Site frequencies in each daughter follow the [time-inhomogeneous Poisson random field](time-inhomogeneous-poisson-random-field-with-legacy-polymorphisms.md) with legacy measure $\nu$ inherited from the ancestor. An alignment holds $m$ sequences from one species and $n$ from the other. Each site is a fixed difference ($K$; monomorphic within each sample at different nucleotides), polymorphic in only one sample ($O$), or polymorphic in both ($H$), giving the table

$$
\begin{bmatrix}K_s & O_s & H_s\\ K_r & O_r & H_r\end{bmatrix},\qquad V_s=O_s+H_s,\quad V_r=O_r+H_r .
$$

For a legacy site at ancestral frequency $x$ and a sample of size $n$, the probabilities of being monomorphic for the original nucleotide, polymorphic, or monomorphic for the mutant are

$$
I(x,n)=P_x(T_0\le t)+\int_0^1p(t,x,y)(1-y)^n\,m(dy),\qquad J(x,n)=\int_0^1p(t,x,y)\big(1-y^n-(1-y)^n\big)\,m(dy),
$$

$$
K(x,n)=P_x(T_1\le t)+\int_0^1p(t,x,y)\,y^n\,m(dy).
$$

Let $C_1(\beta)=\int\big(I(x,m)K(x,n)+I(x,n)K(x,m)\big)\nu(dx)$, $C_2(\beta)=\int\big(J(x,m)+J(x,n)-2J(x,m)J(x,n)\big)\nu(dx)$, and $C_3(\beta)=\int J(x,m)J(x,n)\,\nu(dx)$. For new mutations in one daughter, with density $f_N(\beta,y)=\frac{\theta}{s(1)}\big(s(1)-s(y)-\int_0^1(s(1)-s(x))p(t,x,y)\,m(dx)\big)$ with respect to $m(dy)$, let

$$
E_N(\beta,n)=\int_0^1f_N(\beta,y)\big(1-y^n-(1-y)^n\big)\,m(dy),\qquad D_N(\beta,n)=\frac{\theta}{s(1)}\int_0^t\widetilde P_0(T_1\le u)\,du+\int_0^1f_N(\beta,y)\,y^n\,m(dy).
$$

**Theorem.** The six counts $K_s,O_s,H_s,K_r,O_r,H_r$ are independent Poisson random variables with means, for $\beta\in\{\beta_s,\beta_r\}$,

$$
\mathbb{E}K=C_1(\beta)+D_N(\beta,m)+D_N(\beta,n),\qquad \mathbb{E}O=C_2(\beta)+E_N(\beta,m)+E_N(\beta,n),\qquad \mathbb{E}H=C_3(\beta).
$$

**Corollary.** The classical $2\times2$ McDonald–Kreitman counts $K_s,V_s,K_r,V_r$ are independent Poisson with $\mathbb{E}V=\mathbb{E}O+\mathbb{E}H$.

Shared polymorphisms ($H$) arise only from legacy sites, because a new mutation at a site that never mutates again can be polymorphic in only one daughter species. Independence makes the likelihood a product of Poisson terms, so $(t,\theta_s,\theta_r,\gamma)$ can be estimated by maximum likelihood from these tables.

## Depends on

- [Time-inhomogeneous Poisson random field with legacy polymorphisms](time-inhomogeneous-poisson-random-field-with-legacy-polymorphisms.md)

## Expansion

Conditioning on the population frequency $y$ at time $t$ and sampling binomially gives $I,J,K$, with the hitting-time terms from population loss or fixation. The two daughter populations evolve independently from the same legacy frequency $x$, so each legacy site is independently mapped to one of the outcomes "fixed difference", "polymorphic in one sample", "polymorphic in both", or "uninformative", with the product probabilities above; Bartlett's (marking) theorem for Poisson random fields makes the outcome counts independent Poisson with means $C_1,C_2,C_3$. New mutations form independent Poisson fields in each daughter; binomial thinning gives $E_N$ for sample polymorphisms and $D_N$ for population fixations plus sample-monomorphic mutant sites, which appear as fixed differences against the other species.

## Sources

- Amei Amei and Stanley Sawyer, *A time-dependent Poisson random field model for polymorphism within and between two related biological species*, Annals of Applied Probability 20 (2010), 1663–1696, <https://doi.org/10.1214/09-AAP668>; arXiv:1011.1724, Lemmas 3.1–3.3, Theorem 3.1, Corollary 3.1, equations (3.4)–(3.8). <https://doi.org/10.48550/arXiv.1011.1724>
