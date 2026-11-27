# Survival asymptotics of a decomposable branching process with a subcritical random-environment type

**Model.** A two-type Bienaymé–Galton–Watson process $(X_n, Z_n)$ starts from one type 1 individual. Type 2 individuals reproduce independently with a fixed offspring generating function $h$ that is critical with finite variance:

$$ m_1 = h'(1) = 1, \qquad m_2 = h''(1) \in (0, \infty). $$

Type 1 individuals in generation $n$ produce type 1 and type 2 daughters $(\xi_1, \xi_2)$ according to a random bivariate generating function $f_n(s_1, s_2) = \mathbb E[s_1^{\xi_1}s_2^{\xi_2}]$, the $f_n$ being drawn i.i.d. from a law on generating functions (an IID random environment acting only on type 1). Write $\mu_1 = \partial_1 f(1,1)$, $\mu_2 = \partial_1^2 f(1,1)$, $\theta_1 = \partial_2 f(1,1)$, $\theta_2 = \partial_2^2 f(1,1)$ for the (random) factorial moments and $\zeta = \log\mu_1$. Assume the type 1 line is subcritical in the random environment,

$$ \mathbb E[\zeta] < 0, \qquad \mathrm{Var}[\zeta] \in (0,\infty), $$

that there is $\kappa \in (0,\infty)$ with $\mathbb E[\mu_1^\kappa] = 1$, that $0 < \mathbb E[\xi_2^{\kappa+\delta}] < \infty$ and $\mathbb E[\theta_1^\kappa] < \infty$ for some $\delta > 0$, and either $\kappa > 1$ with $\mathbb E|\xi_1|^\kappa < \infty$, or $0 < \kappa \le 1$ with $\mathbb E\big[|\mu_2 - \mu_1^2|^\kappa + |\theta_2 - \theta_1^2|^\kappa\big] < \infty$.

**Theorem.** There is a constant $K_\kappa \in (0,\infty)$ such that

$$ \mathbb P[Z_n > 0] \sim K_\kappa\, q_\kappa(n), \qquad q_\kappa(n) = \begin{cases} n^{-\kappa}, & \kappa < 1,\\ n^{-1}\log n, & \kappa = 1,\\ n^{-1}, & \kappa > 1,\end{cases} \qquad n \to \infty . $$

Since the type 1 population dies out geometrically fast ($\mathbb P[X_n > 0] = o(A^n)$ for some $A \in (0,1)$), the same asymptotics hold for $\mathbb P[X_n + Z_n > 0]$. An analogous statement holds when the environment is a Markov chain, with $\kappa$ replaced by the corresponding constant of the process embedded at the return times of the environment, under an additional tail condition on those return times.

## Expansion

Let $W_T$ be the total number of type 2 daughters ever produced by the (finitely many) type 1 individuals. A critical type 2 family survives $n$ generations with probability $1 - Q_n \sim 2/(m_2 n)$, so conditionally on the type 1 history $\mathbb P[Z_n > 0]$ is roughly $1 - \exp(-\sum_k Y_k\,a_{n-k})$ with $a_j \sim 2/(m_2 j)$ and $Y_k$ the migrants produced in generation $k$; since the type 1 line lives only $O(1)$ generations, this is close to $\mathbb E\big[1 - e^{-2W_T/(m_2 n)}\big]$. Under the Cramér-type condition $\mathbb E[\mu_1^\kappa] = 1$, the total progeny of a subcritical branching process in random environment has a regularly varying tail, $\mathbb P[W_T > x] \sim C_\kappa x^{-\kappa}$ (Vatutin), and a Tauberian evaluation of $\mathbb E[1 - e^{-W_T/x}]$ for such a tail gives $x^{-\kappa}$ when $\kappa < 1$, $x^{-1}\log x$ when $\kappa = 1$, and $\mathbb E[W_T]/x$ when $\kappa > 1$, with $x \asymp n$. Heavy tails of $W_T$ come from rare favourable environments in which the type 1 population becomes large before dying out, which is why survival can decay more slowly than $1/n$.

## Sources

- Vladimir Vatutin, Elena Dyakonova, Peter Jagers, Serik Sagitov, "A decomposable branching process in a Markovian environment", arXiv:1209.6596 (2012), Section 2 (decomposable processes in constant environment), Section 3 (IID and Markovian environments, Lemma 1), Section 5 (subcritical IID case, Theorem 4), Section 7 (subcritical Markovian case, Theorem 6). <https://doi.org/10.48550/arXiv.1209.6596>. Published version: International Journal of Stochastic Analysis 2012 (2012), 1–24, <https://doi.org/10.1155/2012/694285>; locators above refer to the arXiv version.
