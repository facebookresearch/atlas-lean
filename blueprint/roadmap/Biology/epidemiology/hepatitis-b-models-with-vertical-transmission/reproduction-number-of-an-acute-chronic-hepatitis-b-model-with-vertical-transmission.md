# Reproduction number of an acute–chronic hepatitis B model with vertical transmission and saturated treatment

**Model.** The population is split into susceptible $S$, acutely infected $A$, chronic carriers $C$ and recovered or immune $R$. Parameters: recruitment $\lambda$, a fraction $\alpha C$ of which is born infected (vertical transmission); natural death $\mu$; transmission from carriers $\beta$, with a symmetric saturating incidence $2SC/(S+C)$; transmission from acute cases $\gamma$, with mass action; spontaneous acute recovery $\sigma$; progression to chronicity $\theta$; disease mortality $\rho$; vaccination $u_1$; and treatment $u_2$ with boosting factor $r$ and saturation constant $\phi$. The dynamics are

$$\begin{aligned}
\dot S&=\lambda(1-\alpha C)-\beta\frac{2SC}{S+C}-\gamma AS-u_1S-\mu S,\\
\dot A&=\gamma AS+\beta\frac{2SC}{S+C}-(\sigma+\theta+\mu)A,\\
\dot C&=\theta A+\lambda\alpha C-\Big(\mu+\rho+\frac{ru_2}{1+\phi^2}\Big)C,\\
\dot R&=\sigma A+\frac{ru_2}{1+\phi^2}C+u_1S-\mu R .
\end{aligned}$$

**Statement.** Assume $D:=\rho+\mu+\frac{ru_2}{1+\phi^2}-\alpha\lambda>0$, so that vertical transmission alone cannot sustain the carrier class.

1. Solutions with positive initial data stay positive, and the total population $N=S+A+C+R$ is bounded, with $\limsup_{t\to\infty} N\le\lambda/\mu$.
2. The disease-free equilibrium is $E^0=\big(\frac{\lambda}{\mu+u_1},\,0,\,0,\,\frac{u_1\lambda}{\mu(\mu+u_1)}\big)$.
3. With new infections $\mathcal F$ and transitions $\mathcal V$ in the infected block $(A,C)$, the next-generation matrix at $E^0$ has a single nonzero eigenvalue. So

$$\mathcal R_0=\mathcal R_0^A+\mathcal R_0^C,\qquad \mathcal R_0^A=\frac{\gamma\lambda}{(\sigma+\theta+\mu)(\mu+u_1)},\qquad \mathcal R_0^C=\frac{2\beta\theta}{(\sigma+\theta+\mu)\,D}.$$

Here $\mathcal R_0^A$ counts infections caused directly by an acute case. $\mathcal R_0^C$ counts those caused through the chronic stage it enters with probability $\theta/(\sigma+\theta+\mu)$, during a carrier lifetime of mean $1/D$ shortened by treatment and lengthened by vertical transmission.
4. $E^0$ is locally asymptotically stable if $\mathcal R_0<1$ and unstable if $\mathcal R_0>1$. A linear Lyapunov function $L=d_1(S-S^0)+d_2A+d_3C$ is used to argue global stability for $\mathcal R_0<1$. For $\mathcal R_0>1$ there is an endemic equilibrium, claimed locally and globally asymptotically stable.
5. Treat vaccination $u_1(t)$ and treatment $u_2(t)$ as time-dependent controls in $[0,1]$, minimizing $J=\int_0^{T_f}\big(k_1A+k_2C+\tfrac12w_1u_1^2+\tfrac12w_2u_2^2\big)\,dt$. Pontryagin's maximum principle characterizes the optimal controls as truncations to $[0,1]$ of the stationary points of the Hamiltonian, for example $u_1^*=\min\{\max\{0,(\lambda_4-\lambda_1)S/w_1\},1\}$ with adjoint variables $\lambda_j$.

## Expansion

At $E^0$, the incidence $2\beta SC/(S+C)$ has derivative $2\beta$ in $C$ and $0$ in $S$, so

$$F=\begin{pmatrix}\gamma S^0&2\beta\\0&0\end{pmatrix},\qquad V=\begin{pmatrix}\sigma+\theta+\mu&0\\-\theta&D\end{pmatrix}.$$

The second row of $FV^{-1}$ vanishes, so its spectral radius is the $(1,1)$ entry, which gives the additive decomposition of $\mathcal R_0$. Vertical transmission enters only through $D$: it acts like a negative removal rate for carriers, which is why $D>0$ is needed. The paper also runs a global sensitivity analysis of $\mathcal R_0$ by Latin hypercube sampling with partial rank correlation coefficients. Boundedness follows from $\dot N=\lambda-\mu N-\rho C\le\lambda-\mu N$.

These are the positivity and boundedness theorems (Section 3), the disease-free equilibrium (Section 4), $\mathcal R_0$ (Section 6), the stability theorems (Section 7) and the optimal control problem (Section 8) of the source.

## Sources

- M. Ahmad, A. S. Bhadauria, "A Novel Hepatitis B Epidemic Model with Vertical Transmission, Spontaneous Recovery and Optimal Control Analysis", arXiv:2607.25601 (2026). <https://doi.org/10.48550/arXiv.2607.25601>
