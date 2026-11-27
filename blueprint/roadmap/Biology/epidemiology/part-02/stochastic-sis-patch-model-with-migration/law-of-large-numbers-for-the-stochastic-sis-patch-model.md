# Law of large numbers for the stochastic SIS patch model

**Model.** A population of $N$ individuals is distributed over $\ell$ patches. Let $S_j(t)$ and $I_j(t)$ be the numbers of susceptible and infectious individuals in patch $j$. The process is a Markov jump process driven by independent standard Poisson processes, with the following transitions:

- infection in patch $j$ ($S_j \to S_j-1$, $I_j \to I_j+1$) at rate $\lambda_j S_j I_j/(S_j+I_j)$, where $\lambda_j = \alpha_j p_j$ is the contact rate times the per-contact transmission probability;
- recovery in patch $j$ ($I_j \to I_j-1$, $S_j \to S_j+1$) at rate $\gamma_j I_j$;
- migration of a susceptible from patch $j$ to patch $k$ at rate $\nu_S a_{jk} S_j$, and of an infectious individual at rate $\nu_I a_{jk} I_j$, where $a_{jk} \ge 0$ is the connectivity matrix and $\nu_S, \nu_I > 0$ are the migration coefficients.

Write $\mathcal{Z}^N(t) = (S^N(t), I^N(t))$ with $S^N_j = S_j/N$ and $I^N_j = I_j/N$, and assume $\mathcal{Z}^N(0) = [Nx]/N$ for a fixed $x \in [0,1]^{2\ell}$.

**Theorem.** Let $z(t) = (s_1, i_1, \dots, s_\ell, i_\ell)(t)$ be the unique solution with $z(0) = x$ of

$$\frac{ds_j}{dt} = -\lambda_j\frac{s_j i_j}{s_j+i_j} + \gamma_j i_j + \nu_S\sum_{k\neq j}\big(a_{kj}s_k - a_{jk}s_j\big),$$

$$\frac{di_j}{dt} = \lambda_j\frac{s_j i_j}{s_j+i_j} - \gamma_j i_j + \nu_I\sum_{k\neq j}\big(a_{kj}i_k - a_{jk}i_j\big), \qquad j = 1,\dots,\ell.$$

Then for every fixed $T > 0$,

$$\sup_{0\le t\le T}\big\|\mathcal{Z}^N(t) - z(t)\big\|_1 \longrightarrow 0 \quad \text{almost surely as } N \to \infty.$$

Here $s_j(t)$ and $i_j(t)$ are the fractions of the whole population that are susceptible and infectious in patch $j$.

## Expansion

Writing each Poisson process as $P_j(t) = M_j(t) + t$ gives the semimartingale form

$$\mathcal{Z}^N(t) = \mathcal{Z}^N(0) + \int_0^t b(\mathcal{Z}^N(r))\,dr + \sum_j \frac{h_j}{N} M_j\Big(N\int_0^t \beta_j(\mathcal{Z}^N(r))\,dr\Big),$$

where $h_j \in \{-1,0,1\}^{2\ell}$ are the jump directions, $\beta_j$ the jump rates and $b = \sum_j h_j\beta_j$ the drift of the ODE. The rates are Lipschitz on the region where the process lives (the frequency-dependent term $si/(s+i)$ is bounded by $\min(s,i)$), so the martingale terms vanish uniformly on $[0,T]$ by the strong law of large numbers for Poisson processes, and Gronwall's inequality transfers this to the state. This is the Kurtz-type law of large numbers for density-dependent jump processes, applied to a metapopulation SIS model.

## Proof depends on

- [Kurtz's pathwise estimate for a stochastic reaction network](../../../../Chemistry/chemical-kinetics/kurtz-s-law-of-large-numbers-for-reaction-networ/deviation-le.md)
- [Functional law of large numbers for the unit Poisson process](../../../../Probability/point-processes/poisson-processes/functional-lln-and-clt-for-the-unit-poisson-proc.md)
- [Gronwall inequality in integral form](../../../../Analysis/ordinary-differential-equations/gronwall-inequality/gronwall-inequality-integral-form.md)

## Sources

- T. Yeo, "Stochastic and deterministic SIS patch model", arXiv:2007.07583 (2020), Section 2 (model and Theorem 2.1, law of large numbers), <https://doi.org/10.48550/arXiv.2007.07583>.
