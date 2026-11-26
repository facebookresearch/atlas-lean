# Global stability of the SEIR model with Coxian-distributed incubation

**Model.** The incubation period is Coxian: an exposed individual enters stage $E_n$, leaves stage $E_i$ at rate $\lambda_i$, and on leaving becomes infectious with probability $p_{i-1}$ or moves to stage $E_{i-1}$ with probability $\bar p_{i-1}=1-p_{i-1}$; from the last stage $E_1$ it becomes infectious with probability $p_0=1$. With normalized population, birth and death rate $\mu$, contact rate $\bar\beta$ and recovery rate $\gamma$,

$$
\begin{aligned}
S'&=\mu-\bar\beta SI-\mu S, & E_n'&=\bar\beta SI-(\lambda_n+\mu)E_n,\\
E_i'&=\bar p_i\lambda_{i+1}E_{i+1}-(\lambda_i+\mu)E_i\ \ (i=n-1,\dots,1), & I'&=\sum_{i=0}^{n-1}p_i\lambda_{i+1}E_{i+1}-(\gamma+\mu)I,
\end{aligned}
$$

and $R'=\gamma I-\mu R$, on the invariant simplex $\Omega=\{S+\sum_jE_j+I+R=1\}$.

**Basic reproduction number.**

$$
R_0=\frac{\bar\beta}{\gamma+\mu}\sum_{i=0}^{n-1}a_i\prod_{k=1}^{n-i}\frac{\lambda_{n+1-k}}{\lambda_{n+1-k}+\mu},\qquad a_i=p_i\prod_{j=1}^{n-1-i}\bar p_{j+i},
$$

which equals $\frac{\bar\beta}{\gamma+\mu}(\mathcal Lf_X)(\mu)$, the Laplace transform of the incubation density at $\mu$ (the probability of surviving incubation); for $\mu=0$, $R_0=\bar\beta/\gamma$.

**Theorem.** If $R_0\le1$ the disease-free equilibrium is globally asymptotically stable in $\Omega$. If $R_0>1$ there is a unique endemic equilibrium, and it is globally asymptotically stable in the interior of $\Omega$; no endemic equilibrium exists when $R_0\le1$.

## Expansion

A Coxian distribution is a phase-type law: a chain of exponential stages with early exits, dense among positive distributions, so it can match empirical incubation-period data (the source fits COVID-19-like data) while keeping an ODE model. The product formula is the probability of reaching $I$ alive, summed over the exit stage. Global stability uses Volterra-type Lyapunov functions $\sum_ic_i(x_i-x_i^*\ln x_i)$ with weights proportional to the probability of eventually becoming infectious from each stage, generalizing the SEIR proof; the graph-theoretic structure of the stage chain makes the cross terms cancel.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Proof depends on

- [LaSalle's invariance principle](../../../../Dynamics/smooth-dynamics/lasalle-s-invariance-principle/lasalle.md)

## Sources

- Sungchan Kim, Jong Hyuk Byun, Il Hyo Jung, "Global Stability of an SEIR Epidemic Model where Empirical Distribution of Incubation Period has Approximated by Coxian Distribution", arXiv:1906.05556: Section 2 (derivation of the Coxian SEIR model), Section 3 (basic reproduction number), Section 4: Theorems 1–3. <https://doi.org/10.48550/arXiv.1906.05556>
