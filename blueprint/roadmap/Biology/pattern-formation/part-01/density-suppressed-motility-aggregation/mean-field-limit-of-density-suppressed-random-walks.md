# Mean-field limit of density-suppressed random walks

**Individual-based model.** Individuals at positions $x_i(t)\in\mathbb R^d$, $i=1,\dots,N$, sense the average density

$$\vartheta_i=\frac1N\sum_{j\ne i}W(x_i-x_j),$$

with $W(x)=w(|x|)$ bounded, nonnegative, nonincreasing and integrable (e.g. the indicator of a sampling radius $R$), and move by a density-dependent random walk

$$dx_i=G(\vartheta_i)\,dB^i_t,$$

with independent Brownian motions $B^i$ and $G:\mathbb R_+\to\mathbb R_+$ bounded, nonnegative and nonincreasing (degeneracy $G=0$ allowed). In a second-order variant velocities obey $dv_i=-H(\vartheta_i)v_i\,dt+G(\vartheta_i)\,dB^i_t$ with nondecreasing damping $H$.

**Mean-field equation.** As $N\to\infty$ (formally, for $W\in C^1$) the density $\varrho(t,x)$ satisfies the nonlocal nonlinear diffusion

$$\partial_t\varrho=\Delta\big(F(W*\varrho)\,\varrho\big),\qquad F=\tfrac12G^2,$$

The diffusive limit of the kinetic Fokker–Planck equation of the second-order model is $\partial_t\varrho=\frac d2\nabla\cdot\bigl(H(W*\varrho)^{-1}\nabla(T\varrho)\bigr)$ with local temperature $T=G(W*\varrho)^2/(2H(W*\varrho))$ (source Eq. (3.13)); for constant $H$ it is the mean-field equation up to a linear rescaling of time.

**Theorem.** Let $F$ be bounded, nonnegative, nonincreasing and $C^1$ with globally Lipschitz derivative, with $G=\sqrt{2F}$ globally Lipschitz, and let $W\in W^{1,\infty}(\mathbb R^d)\cap H^2(\mathbb R^d)$.

1. For $\varrho_0\in L^2(\mathbb R^d)\cap\mathcal P(\mathbb R^d)$ and $T>0$ there is a weak solution $\varrho\in L^\infty(0,T;L^2)\cap L^\infty(0,T;\mathcal P)\cap H^1(0,T;H^{-1})$ with $F(W*\varrho)\varrho\in L^2(0,T;H^1)$.
2. For any probability measure $\varrho_0\in\mathcal P(\mathbb R^d)$ there is a very weak (distributional) solution $\varrho\in L^\infty(0,T;\mathcal P)$.
3. If $G(s)=0$ for all $s\ge s_0$ and $W$ is continuous, every atomic measure $\varrho=\sum_{i=1}^Nc_i\delta_{x_i}$ with $c_iW(0)>s_0$ for all $i$ is a stationary distributional solution.

## Expansion

There is no aggregative drift in the particle model; aggregation comes from Itô-type diffusion $\Delta(F\varrho)$: writing it as $\nabla\cdot(\varrho\nabla F(W*\varrho)+F(W*\varrho)\nabla\varrho)$, the first term transports mass up the perceived-density gradient because $F$ is decreasing. Existence is proved by regularizing $F_\varepsilon=F+\varepsilon$ (uniformly parabolic, Schauder fixed point), $\varepsilon$-uniform $L^2$ and $H^1$ estimates, and Aubin–Lions compactness of $W*\varrho_\varepsilon$; measure data follow by tight approximation. Atoms heavy enough to push the perceived density above $s_0$ freeze their own motility, so clumps are exactly stationary; simulations with $G>0$ show localized but not compactly supported aggregates.

## Sources

- M. Burger, J. Haškovec, M.-T. Wolfram, "Individual based and mean-field modeling of direct aggregation", *Physica D* (2013), Sections 2–4: equations (2.1)–(2.5), (3.4), (3.5), (3.11), (4.1), Definitions 1 and 2, Theorems 1 and 2, Section 4.3, <https://doi.org/10.1016/j.physd.2012.11.003>, PMCID: PMC4047626.
