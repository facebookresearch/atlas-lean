# Global stability of the SEIAR model with newborn vaccination

**Model.** In a population of constant size $N$ with birth and death rate $\mu$, let $S,E,I,A,R$ be susceptible, exposed, symptomatic infectious, asymptomatic infectious and recovered individuals. A fraction $p$ of newborns enters a vaccinated class $V$ with a leaky vaccine of efficacy $\epsilon\in[0,1]$:

$$
\begin{aligned}
S'&=(1-p)\mu N-\beta_ISI-\beta_ASA-\mu S, & V'&=p\mu N-(1-\epsilon)(\beta_IVI+\beta_AVA)-\mu V,\\
E'&=\big(S+(1-\epsilon)V\big)(\beta_II+\beta_AA)-(k+\mu)E, & I'&=k(1-q)E-(\gamma_I+\mu)I,\\
A'&=kqE-(\gamma_A+\mu)A, & R'&=\gamma_II+\gamma_AA-\mu R,
\end{aligned}
$$

with incubation rate $k$, asymptomatic fraction $q$, recovery rates $\gamma_I,\gamma_A$ and transmission rates $\beta_I,\beta_A$. The case $p=0$ is the SEIAR model.

**Reproduction numbers.**

$$
\mathcal R_0=\frac{\beta_INk(1-q)}{(k+\mu)(\gamma_I+\mu)}+\frac{\beta_ANkq}{(k+\mu)(\gamma_A+\mu)},\qquad \mathcal R_0^V=(1-\epsilon p)\,\mathcal R_0.
$$

**Theorem.**
1. Without vaccination, the disease-free state $(N,0,0,0,0)$ is globally asymptotically stable if $\mathcal R_0\le1$, and if $\mathcal R_0>1$ the unique endemic state with $S^*=N/\mathcal R_0$, $E^*=\frac{N\mu}{k+\mu}(1-1/\mathcal R_0)$, $I^*=\frac{Nk(1-q)\mu}{(\gamma_I+\mu)(k+\mu)}(1-1/\mathcal R_0)$, $A^*=\frac{Nkq\mu}{(\gamma_A+\mu)(k+\mu)}(1-1/\mathcal R_0)$ is globally asymptotically stable.
2. With vaccination, the disease-free state $((1-p)N,pN,0,0,0,0)$ is globally asymptotically stable if $\mathcal R_0^V\le1$, and if $\mathcal R_0^V>1$ the endemic state, with $S^*=(1-p)N/\mathcal R_0^V$, $V^*=pN/\mathcal R_0^V$ and $E^*,I^*,A^*$ as above with $\mathcal R_0$ replaced by $\mathcal R_0^V$ and $I^*,A^*$ multiplied by $1-\epsilon p$, is globally asymptotically stable.

## Expansion

$\mathcal R_0$ is the next-generation spectral radius: an exposed individual becomes symptomatic with probability $k(1-q)/(k+\mu)$ and then infects $\beta_IN/(\gamma_I+\mu)$ others, and similarly for the asymptomatic route. Vaccination at birth with leaky efficacy removes a fraction $\epsilon p$ of the effective susceptible pool, so coverage and efficacy act multiplicatively, $\mathcal R_0^V=(1-\epsilon p)\mathcal R_0$; elimination requires $\epsilon p>1-1/\mathcal R_0$. Global stability uses Lyapunov functions of Volterra type $\sum c_i(x_i-x_i^*\ln x_i)$ combined with LaSalle's invariance principle, extending the classical SEIR argument to the two parallel infectious classes.

## Depends on

- [Next-generation matrix and the basic reproduction number](../next-generation-matrix-and-the-basic-reproductio/r0.md)
- [Global stability of the SEIR model](../global-stability-of-the-seir-model/README.md)

## Sources

- Vasiliki Bitsouni, Nikolaos Gialelis, Ioannis G. Stratis, "A model for the outbreak of COVID-19: Vaccine effectiveness in a case study of Italy", arXiv:2008.00828: Section 2 (SEIAR model, reproduction number, Theorems 1–4 on local and global stability) and Section 3 (SVEIAR model, vaccinated reproduction number, Theorems 5–6). <https://doi.org/10.48550/arXiv.2008.00828>
