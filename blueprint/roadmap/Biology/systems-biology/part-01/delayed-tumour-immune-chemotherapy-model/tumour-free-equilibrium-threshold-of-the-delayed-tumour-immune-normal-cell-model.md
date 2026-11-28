# Tumour-free equilibrium threshold of the delayed tumour-immune-normal cell model

**Model.** Let $E(t)$ be activated effector immune cells, $T(t)$ tumour cells and $N(t)$ normal cells, with a recruitment delay $\tau\ge 0$ and no drug ($u\equiv 0$):

$$
\begin{aligned}
E'(t)&=\sigma+\frac{\rho E(t-\tau)T(t-\tau)}{\eta+T(t-\tau)}-\mu E(t-\tau)T(t-\tau)-\delta E(t),\\
T'(t)&=r_2T(t)\bigl(1-\beta T(t)\bigr)-nE(t)T(t)-c_1N(t)T(t),\\
N'(t)&=r_3N(t)\bigl(1-\beta_2N(t)\bigr)-c_2T(t)N(t),
\end{aligned}
$$

with all parameters positive, continuous nonnegative initial functions on $[-\tau,0]$, and normalization $\beta_2=1$.

**Statement.** The tumour-free steady state is $E_0=(\sigma/\delta,\,0,\,1)$. Its linearization has eigenvalues

$$
\lambda_1=-\delta,\qquad \lambda_2=r_2-\frac{n\sigma}{\delta}-c_1,\qquad \lambda_3=-r_3,
$$

independently of $\tau$ (the delayed terms enter only through an entry that does not affect the triangular spectrum). Hence $E_0$ is locally asymptotically stable for every delay $\tau\ge 0$ if

$$
r_2<\frac{n\sigma}{\delta}+c_1 ,
$$

and unstable if $\lambda_2>0$, i.e. if $r_2>n\sigma/\delta+c_1$; at $\lambda_2=0$ the linearization does not decide. (The source states the sufficient direction: "$E_0$ is locally stable if $\lambda_2<0$ if and only if $r_2<n\sigma/\delta+c_1$, $\forall\tau\ge0$", Eq. (13).)

The lethal state $(\sigma/\delta,0,0)$ has eigenvalues $-\delta$, $r_2-n\sigma/\delta$ and $r_3>0$, so it is always an unstable saddle.

## Expansion

At $E_0$ the factor $T$ multiplies every delayed term, so the characteristic matrix is upper triangular apart from $e^{-\lambda\tau}$ factors in the $(E,T)$ entry, and the delay cannot move the eigenvalues. The quantity $n\sigma/\delta$ is the per-capita kill exerted by the tumour-free immune equilibrium $\sigma/\delta$; the condition says immune kill plus competition from normal tissue must exceed intrinsic tumour growth. If the condition fails, no therapy can drive the system to a stable tumour-free state, which motivates the optimal control formulation of the companion article. Coexisting equilibria $(f(T^*),T^*,1-(c_2/r_3)T^*)$ solve a cubic in $T^*$ and can number zero to three; for those, stability can be lost at a critical delay through a Hopf bifurcation.

## Sources

- Rihan FA, Abdelrahman DH, Al-Maskari F, Ibrahim F, Abdeen MA. Delay differential model for tumour-immune response with chemoimmunotherapy and optimal control. *Computational and Mathematical Methods in Medicine* (2014) 982978. <https://doi.org/10.1155/2014/982978>. PMCID: PMC4147205. Section 3.1, Eqs. (12)-(13); Section 3.2.
