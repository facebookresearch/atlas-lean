# Persistence threshold for phase-structured metapopulations on dynamic landscapes

Consider the [large-metapopulation limit of the incidence function model with Markovian landscape dynamics](large-metapopulation-limit-with-markovian-landscape-dynamics.md), with occupancy recursion $q_t(\theta,z)$. Assume in addition **phase structure** (extinction and colonization phases alternate, observations after extinction), i.e. the colonization function factorizes as $f(x;\theta)=s(\theta)\bar f(x;\theta)$ with $\bar f(\cdot;\theta):[0,\infty)\to[0,1]$ **concave** for each $\theta$ (no Allee-like effect), together with $s<1$ and the condition that from some colonizable state the landscape moves with positive probability to a state with $a>0$. Let $(\theta_t)_{t\ge0}$ be the stationary landscape chain and define the species-specific factor and the dispersal operator

$$r_S=\sum_{m=1}^{\infty}\mathbb E\Bigl\{\bar f'(0;\theta_0)\Bigl[\prod_{k=0}^{m-1}s(\theta_k)\Bigr]a(\theta_m)\Bigr\},\qquad \mathcal M\phi(z)=\int_\Omega D(z,\tilde z)\,\phi(\tilde z)\,\zeta(\tilde z)\,d\tilde z,$$

with $r(\mathcal M)$ the spectral radius of $\mathcal M$ on $C(\Omega)$.

**Theorem (persistence dichotomy).** If $r_S\,r(\mathcal M)\le1$, the recursion has only the trivial fixed point $q\equiv0$, and it is globally stable. If $r_S\,r(\mathcal M)>1$, the recursion has a unique non-zero fixed point $q^\ast$, and $q_t\to q^\ast$ whenever $q_0(\theta,z)>0$ on $\Theta\times\Omega$.

**Theorem (effect of landscape dynamics).** Suppose $\bar f(x;\theta)=\bar f(x)$.

1. The equilibrium expected colonized weight $\int_\Theta a(\theta)q^\ast(\theta,z)\pi(d\theta)$ depends on the landscape law $(\pi,P)$ only through the sequence $\mathbb E\bigl(a(\theta_{m+1})\prod_{k=1}^m s(\theta_k)\bigr)$, $m\ge1$.
2. If two landscapes satisfy $\mathbb E\bigl(a(\tilde\theta_{m+1})\prod_{k=1}^ms(\tilde\theta_k)\bigr)\le\mathbb E\bigl(a(\theta_{m+1})\prod_{k=1}^ms(\theta_k)\bigr)$ for all $m\ge1$, their equilibria are ordered in the same way at every location $z$.
3. For a stationary chain, $\mathbb E\bigl(\prod_{k=0}^m s(\theta_k)\bigr)\le\mathbb E\bigl(s(\theta_0)^{m+1}\bigr)$. Hence, among landscape dynamics with a given stationary law and constant patch weights, the static landscape maximizes the local population life span and the equilibrium occupancy.

With $\bar f$ independent of $\theta$ and constant weight $\bar a$, $r_S=\bar a\,\bar f'(0)\sum_{m\ge0}\mathbb E\bigl(\prod_{k=0}^{m-1}s(\theta_k)\bigr)$, i.e. weight times initial colonization slope times the expected life span of a local population, mirroring the factorization of persistence criteria for the spatially realistic Levins model.

## Depends on

- [Large-metapopulation limit of the incidence function model with Markovian landscape dynamics](large-metapopulation-limit-with-markovian-landscape-dynamics.md)

## Expansion

Under phase structure and concavity, the fixed-point map is monotone, strongly sublinear ($T(\lambda q)>\lambda T(q)$ for $0<\lambda<1$), strongly positive, continuous and order compact on a cone of continuous functions. Its derivative at $0$ is a positive linear operator $\mathcal A$ whose spectral radius factorizes as $r(\mathcal A)=r_S\,r(\mathcal M)$: the landscape enters only through expected future contributions to connectivity during a local population's life span, and space only through $\mathcal M$. Krasnosel'skii-type theorems for sublinear monotone maps then give the threshold: if $r(\mathcal A)\le1$, zero is the only fixed point and attracts all orbits; if $r(\mathcal A)>1$, there is exactly one positive fixed point, attracting all strictly positive initial conditions. The bound $\mathbb E\prod s(\theta_k)\le\mathbb E s(\theta_0)^{m+1}$ is a generalized Hölder inequality applied to the identically distributed factors $s(\theta_k)$.

## Sources

- R. McVinish, P. K. Pollett, Y. S. Chan, "A metapopulation model with Markovian landscape dynamics", arXiv (2014). Section 4 (Theorem 4.1, Theorem 4.2, Theorem 4.3, Corollary 4.4), Section 8 (Appendix C: Theorem 8.1, Lemmas 8.2–8.6, Theorems 8.7 and 8.8). <https://doi.org/10.48550/arXiv.1412.0719>. Published version: Theoretical Population Biology 112 (2016), 80–96, <https://doi.org/10.1016/j.tpb.2016.08.005>; locators above refer to the arXiv version.
