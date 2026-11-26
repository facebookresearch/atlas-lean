# Competitive exclusion and bistability in the chemostat with interspecific density-dependent growth

**Model.** Two microbial species $x_1,x_2$ compete for one substrate $S$ in a chemostat with dilution rate $D>0$ and feed concentration $S_{in}>0$. After rescaling biomasses by the yields,
$$
\dot S = D(S_{in}-S) - f_1(S,x_2)x_1 - f_2(S,x_1)x_2,\qquad
\dot x_1 = (f_1(S,x_2)-D_1)x_1,\qquad
\dot x_2 = (f_2(S,x_1)-D_2)x_2,
$$
with removal rates $D_i = \alpha_i D + a_i$ ($\alpha_i\in[0,1]$ decouples solid from hydraulic retention, $a_i\ge 0$ is mortality). Each $f_i:\mathbb{R}_+^2\to\mathbb{R}_+$ is $C^1$ with $f_i(0,x_j) = 0$, $\partial_S f_i>0$ and $\partial_{x_j} f_i<0$ for $S,x_j>0$ ($j\ne i$): growth needs substrate and is inhibited only by the *other* species. Solutions are nonnegative and bounded, and $\{S+x_1+x_2\le DS_{in}/\min(D,D_1,D_2)\}$ is positively invariant and globally attracting.

**Break-even concentrations.** Let $\lambda_i(D)$ solve $f_i(\lambda_i,0) = D_i$, and $\tilde x_i = D(S_{in}-\lambda_i(D))/D_i$.

**Steady states.** Under these hypotheses there are at most four steady states, each unique when it exists:
- washout $\mathcal{E}_0 = (S_{in},0,0)$, always; locally exponentially stable iff $S_{in}<\min(\lambda_1(D),\lambda_2(D))$;
- $\mathcal{E}_1 = (\lambda_1(D),\tilde x_1,0)$ iff $S_{in}>\lambda_1(D)$; stable iff $f_2\big(\lambda_1(D),\, D(S_{in}-\lambda_1(D))/D_1\big)<D_2$;
- $\mathcal{E}_2 = (\lambda_2(D),0,\tilde x_2)$ iff $S_{in}>\lambda_2(D)$; stable iff $f_1\big(\lambda_2(D),\, D(S_{in}-\lambda_2(D))/D_2\big)<D_1$;
- a coexistence state $\mathcal{E}^* = (S^*,x_1^*,x_2^*)$ exists iff both of the last two inequalities hold, i.e. iff $\mathcal{E}_1$ and $\mathcal{E}_2$ both exist and are both stable; it is unique and **always unstable**.

**Consequences.** $\mathcal{E}_0$ is stable iff neither one-species state exists. Whenever $\mathcal{E}^*$ exists the system is bistable: depending on the initial condition, one or the other species is excluded. Interspecific inhibition alone, even with distinct removal rates and mortality, therefore cannot produce stable coexistence on a single resource.

**Operating diagram.** In the $(S_{in},D)$ plane the regions of existence and stability are bounded by the curves $S_{in} = \lambda_1(D)$, $S_{in} = \lambda_2(D)$ and $\tilde x_i(S_{in},D) = \bar x_i(S_{in},D)$, $i=1,2$ (where $\bar x_i$ solves $f_j(S_{in} - D_i x_i/D,\, x_i) = D_j$); steady states appear or disappear across these boundaries only through transcritical bifurcations.

## Expansion

At a coexistence state $x_2 = F_1(x_1) = F_2(x_1)$, where $F_i$ is the zero-growth isocline $f_i(S_{in}-D_1x_1/D - D_2x_2/D,\,x_j) = D_i$ restricted to the conservation plane. Implicit differentiation gives $F_1' = -D_1E/(D_2E+DG)$ and $F_2' = -(D_1F+DH)/(D_2F)$ with $E=\partial_Sf_1$, $F=\partial_Sf_2$, $G=-\partial_{x_2}f_1$, $H=-\partial_{x_1}f_2$ all positive, so both isoclines decrease, and at any crossing $\gamma_1$ is less steep than $\gamma_2$. This slope ordering forces at most one crossing and yields the instability of the coexistence state (the paper proves it from the Jacobian in its appendix). Comparing the axis intercepts $\tilde x_i$, $\bar x_i$ gives the three cases (exclusion by species 1, bistability, exclusion by species 2). With Monod-type rates $f_i = m_iS/(K_i+S+\beta_ix_j)$ the paper constructs the diagram analytically and confirms it with numerical continuation, which also detects codimension-two points.

## Depends on

- [Chemostat equilibria and the washout threshold](../chemostat/chemostat-equilibria-and-washout.md)

## Sources

- T. Mtar, R. Fekih-Salem, "Analysis and operating diagram of an interspecific density-dependent model", arXiv:2401.06339 (2024), Section 2 (model, hypotheses, invariance), Section 3 (isocline lemmas, existence and stability tables and their corollaries) and Section 4 (operating diagram), <https://doi.org/10.48550/arXiv.2401.06339>.
