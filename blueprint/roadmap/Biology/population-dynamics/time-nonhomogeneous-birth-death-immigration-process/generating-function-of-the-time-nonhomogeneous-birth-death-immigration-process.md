# Generating function of the time-nonhomogeneous birth–death–immigration process

**Setting.** Let $I(t)$ be a linear birth–death–immigration (BDI) process: each individual gives birth at rate $\lambda(t)$ and dies at rate $\mu(t)$, and immigrants arrive at rate $\nu(t)$, all locally integrable and non-negative, with $I(0)=I_0$. In epidemic use, $I(t)$ counts infected individuals, with infections, recoveries and imported cases. Put

$$s(t)=\int_0^t(\lambda(u)-\mu(u))\,du,\qquad L(t)=\int_0^t\lambda(u)e^{-s(u)}\,du,\qquad M(t)=\int_0^t\mu(u)e^{-s(u)}\,du,$$

so that $e^{-s(t)}=1-L(t)+M(t)$, and let $G(z,t)=\mathbb E\,z^{I(t)}$, which solves $\partial_tG=(\lambda z-\mu)(z-1)\partial_zG+\nu(z-1)G$.

**Theorem.**
1. (Decomposition) The probability generating function factorizes as

$$G_{BDI:I_0}(z,t)=G_{BD:I_0}(z,t)\;G_{ID:0}(z,t),$$

where the first factor is Kendall's birth–death generating function of the descendants of the initial individuals,

$$G_{BD:I_0}(z,t)=\Big(1+\frac{e^{s(t)}(z-1)}{1-e^{s(t)}L(t)(z-1)}\Big)^{I_0}=\Big(\frac{\alpha(t)+(1-\alpha(t)-\beta(t))z}{1-\beta(t)z}\Big)^{I_0},$$

with $\alpha=M/(1+M)$, $\beta=L/(1+M)$, and the second is the generating function of the immigrants and their descendants,

$$G_{ID:0}(z,t)=\exp\Big(\int_0^t\frac{\nu(u)\,e^{s(t)-s(u)}(z-1)}{1-e^{s(t)}\big(L(t)-L(u)\big)(z-1)}\,du\Big).$$

Equivalently $I(t)=I_{BD:I_0}(t)+I_{ID:0}(t)$ with independent summands.
2. (Negative binomial law) If the immigration-to-birth ratio $r=\nu(t)/\lambda(t)$ is constant and $I_0=0$, then

$$G_{BDI:0}(z,t)=\Big(\frac{1-\beta(t)}{1-\beta(t)z}\Big)^{r},$$

so $I(t)$ is negative binomial with parameters $(r,\beta(t))$ at every time.

## Expansion

The characteristics of the linear first-order PDE give the first integral $e^{-s(t)}/(z-1)-L(t)=C_1$, and along them $d\log G/dt=\nu(t)(z-1)$; substituting $z-1=e^{-s}/(C_1+L)$ makes the right side independent of $z$ and gives the second integral $G\exp(-\int_0^t\nu e^{-s}/(C_1+L)\,du)=C_2$. The initial condition $G(z,0)=z^{I_0}$ fixes $C_2=(1+C_1^{-1})^{I_0}$ and yields the product formula. Probabilistically, immigrants arriving at time $u$ form a Poisson process of rate $\nu(u)$, each founding an independent birth–death family started at $u$, and the Poisson exponential formula gives $G_{ID:0}$. When $\nu=r\lambda$ the integrand equals $r\,\partial_u\log A(u)$ with $A(u)=1-e^{s(t)}(L(t)-L(u))(z-1)$, so the integral is $-r\log(1-e^{s(t)}L(t)(z-1))$, which is the stated negative binomial generating function because $1+M=e^{-s}+L$.

## Sources

- Hisashi Kobayashi, "Stochastic Modeling of an Infectious Disease, Part III-B: Analysis of the Time-Nonhomogeneous BDI Process and Simulation Experiments of both BD and BDI Processes", arXiv:2104.00529 (2021), Section 1, Proposition 1 and Corollary 1, <https://doi.org/10.48550/arXiv.2104.00529>.
