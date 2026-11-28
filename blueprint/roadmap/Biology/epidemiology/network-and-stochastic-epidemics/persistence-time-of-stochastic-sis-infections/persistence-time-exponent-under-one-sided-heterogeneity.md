# Persistence-time exponent of the SIS model under one-sided heterogeneity

**Model.** A closed population of $N$ individuals is divided into $k$ groups with proportions $f_i = N_i/N > 0$, $\sum_i f_i = 1$. Each infective of group $i$ contacts each individual of group $j$ at rate $\beta\lambda_i\mu_j/N$ (separable mixing), with infectivities $\lambda_i > 0$ and susceptibilities $\mu_j > 0$ normalized so that $\sum_i \lambda_i f_i = \sum_j \mu_j f_j = 1$, and infectious periods are exponential with mean $1/\gamma$. The vector $I(t) = (I_1,\dots,I_k)$ of infectives is a continuous-time Markov chain with rates

$$I_j \to I_j + 1 \text{ at rate } \frac{\beta}{N}\Big(\sum_{m=1}^k \lambda_m I_m\Big)\mu_j (N_j - I_j), \qquad I_j \to I_j - 1 \text{ at rate } \gamma I_j,$$

and $R_0 = (\beta/\gamma)\sum_i \lambda_i\mu_i f_i$. Let $\tau$ be the mean time to extinction started from the quasi-stationary distribution.

For a positive vector $x$ with $\sum_j f_j x_j = 1$ let $D(x) > 0$ be the unique positive root of

$$\frac{\beta}{\gamma}\sum_{j=1}^k \frac{f_j x_j}{1 + x_j D(x)} = 1,$$

which exists when $\beta/\gamma > 1$.

**Theorem.** Suppose $R_0 > 1$.
1. (Heterogeneous infectivity only, $\mu \equiv 1$, so $R_0 = \beta/\gamma$.)

$$\lim_{N\to\infty} \frac{\ln \tau}{N} = \sum_{i=1}^k f_i \ln\big(1 + \lambda_i D(\lambda)\big) - \frac{\gamma}{\beta} D(\lambda).$$

2. (Heterogeneous susceptibility only, $\lambda \equiv 1$.) The same formula holds with $\lambda$ replaced by $\mu$.
3. Part 2 remains valid when infectious periods are Erlang rather than exponential.
4. (Directed configuration network, annealed approximation.) If each individual has in-degree exactly $\mu_{\rm deg}$ and out-degree distributed as $d_{\rm out}$ with mean $\mu_{\rm deg}$ and bounded support, transmission occurs at rate $\kappa$ per link and exponential infectious periods have mean $1/\gamma$, then $\ln\tau/N \to A_{\rm out}$ with

$$A_{\rm out} = \sum_{i} P(d_{\rm out} = i)\ln(1 + i D_{\rm out}) - \frac{\gamma}{\kappa}D_{\rm out}, \qquad \frac{\kappa}{\gamma}\sum_j \frac{j\,P(d_{\rm out}=j)}{1 + jD_{\rm out}} = 1,$$

and symmetrically for fixed out-degree and random in-degree (with Erlang infectious periods allowed).

In the homogeneous case $D = R_0 - 1$ and the exponent reduces to the classical value $\ln R_0 - 1 + 1/R_0$.

## Depends on

- [Extinction time of the stochastic logistic SIS epidemic](../../sis-epidemic-model/extinction-time-of-the-stochastic-logistic-epidemic.md)

## Expansion

The exponent is the action $A = U(0) - U(\theta^*)$ of the Hamiltonian $H(y,\theta) = \beta\sum_j\lambda_j y_j\sum_i \mu_i(f_i - y_i)(e^{\theta_i}-1) + \gamma\sum_i y_i(e^{-\theta_i}-1)$ along the optimal path from the endemic point to the extinct state with nonzero momentum $\theta^*$. The nonzero fixed momentum satisfies $e^{-\theta_i^*} = 1 + \lambda_i D$. When $\mu \equiv 1$, the trajectory $\theta_i(z) = -\ln(1+\lambda_i z)$, $0 \le z \le D(\lambda)$, reduces the Hamilton–Jacobi equation $H(\partial U/\partial\theta,\theta) = 0$ to $dU/dz = \gamma/\beta - \sum_i f_i\lambda_i/(1+\lambda_i z)$, which integrates to the formula. Part 2 follows from network duality: for exponential infectious periods the decay parameter of an SIS process is unchanged by transposing the matrix of pairwise infection rates, which swaps $\lambda$ and $\mu$. The network statement is the group model with groups indexed by degree pairs, $\lambda_i \propto d_{\rm out}$, $\mu_j \propto d_{\rm in}$.

## Sources

- D. Clancy, "Persistence time of SIS infections in heterogeneous populations and networks", Journal of Mathematical Biology (2018), Sect. 2 (model, Table 1), Eqs. (13)–(18), Theorems 1, 3 and 4, <https://doi.org/10.1007/s00285-018-1222-1>, PMCID PMC6132977.
