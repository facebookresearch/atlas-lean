# Exact ODE limit of SIR and SEIR epidemics on sparse locally tree-like graphs

**Setting.** On a graph $G_n$ with $n$ vertices, each vertex is susceptible (S), infected (I) or recovered (R); an infected vertex infects each susceptible neighbor at rate $\beta_t$ and recovers at rate $\rho_t$ (time-varying, locally bounded). Initial states are i.i.d., S with probability $s_0 \in (0,1)$ and I otherwise. Let $s^{G_n}(t), i^{G_n}(t)$ be the fractions of S and I vertices. The graph sequence is either Erdős–Rényi $\mathrm{ER}(n,c/n)$ with $\theta = \mathrm{Poisson}(c)$, or a uniform configuration model whose empirical degree law converges to $\theta$ with finite third moment (random $\kappa$-regular graphs being $\theta = \delta_\kappa$). Let $\hat\theta(k) = (k+1)\theta(k+1)/\sum_j j\theta(j)$ be the size-biased law and $M_\zeta(x) = \sum_k \zeta(k)e^{kx}$.

**Proposition.** There is a unique solution $(f_S, f_I, F_I)$ of
$$\begin{cases} \dot f_S = \beta f_S f_I\left(1 - \dfrac{\sum_k k\hat\theta(k)e^{-kF_I}}{\sum_j \hat\theta(j)e^{-jF_I}}\right),\\[2ex] \dot f_I = \beta f_S f_I\,\dfrac{\sum_k k\hat\theta(k)e^{-kF_I}}{\sum_j \hat\theta(j)e^{-jF_I}} - f_I(\rho + \beta - \beta f_I),\\[2ex] \dot F_I = \beta f_I, \end{cases} \qquad (f_S, f_I, F_I)(0) = (s_0, 1-s_0, 0).$$

**Theorem.** Define
$$s^{(\infty)}(t) = s_0\,M_\theta(-F_I(t)), \qquad i^{(\infty)}(t) = e^{-\int_0^t \rho_u du}\left(i_0 + s_0\int_0^t M_\theta'(-F_I(u))\,e^{\int_0^u \rho_r dr}\,\beta_u f_I(u)\,du\right),$$
with $i_0 = 1-s_0$. Then $s^{G_n}(t) \to s^{(\infty)}(t)$ and $i^{G_n}(t) \to i^{(\infty)}(t)$ in probability, uniformly in $t \in [0,\infty)$. An analogous four-dimensional ODE $(g_S, g_E, g_I, G_I)$ describes the SEIR process (exposed vertices become infectious at rate $\lambda_t$), with the same type of convergence.

## Expansion

Sparse locally tree-like graphs converge locally to the unimodular Galton–Watson tree $\mathrm{UGW}(\theta)$, and the empirical state fractions converge to the root marginal of the epidemic on that tree. On the tree the SIR dynamics have a conditional independence property: given that a vertex is still susceptible, the histories of its subtrees evolve independently. This makes the root's law a function of a single scalar, the cumulative infection pressure $F_I(t)$ from one neighbor: $f_I$ is the probability that a given neighbor of a susceptible vertex is infected, $f_S$ that it is susceptible, so a degree-$k$ root survives with probability $e^{-kF_I}$ and averaging over $\theta$ gives $s^{(\infty)} = s_0 M_\theta(-F_I)$. The ODE is exact, not a pair approximation, on these graph ensembles.

## Sources

- J. Cocomello, K. Ramanan, "Exact description of limiting SIR and SEIR dynamics on locally tree-like graphs", arXiv:2309.08829 (2023), Assumption 2, Propositions 2.4 and 2.9, Theorems 2.5 and 2.10 (Section 2), Theorems 4.5, 4.10 and 4.12 (Section 4), <https://doi.org/10.48550/arXiv.2309.08829>.
