# Stochastic growth rate of random products of projection matrices

Let the environment $e_t$ follow either an i.i.d. sequence with distribution $\nu$ on a finite set of environments, all $\nu_e > 0$, or an ergodic (irreducible and aperiodic) Markov chain on that set started in its stationary distribution, and let $X_e$ be nonnegative $K \times K$ population projection matrices such that (i) every row of every $X_e$ has a positive entry and (ii) there is $R > 0$ such that every product $X_{e_1} \cdots X_{e_R}$ is positive. For the population $N_t = X_{e_t} X_{e_{t-1}} \cdots X_{e_1} N_0$ with $N_0$ positive, the limit

$$a = \lim_{t \to \infty} \frac1t \log N_t(i) = \lim_{t \to \infty} \frac1t \log \frac{\sum_i N_t(i)}{\sum_i N_0(i)}$$

exists almost surely and is deterministic: almost every realization gives the same value, for every stage $i$, because the environmental process is ergodic; it is the stochastic growth rate, the leading Lyapunov exponent of the random matrix product (Steinsaltz, Tuljapurkar and Horvitz, Section 2, under the conditions above). The normalized structure $N_t/\sum_i N_t(i)$ need not converge almost surely; it converges in distribution. The existence of the leading Lyapunov exponent goes back to Furstenberg and Kesten (1960).

## Proof depends on

- [Kingman's subadditive ergodic theorem](../../../Dynamics/ergodic-theory/kingman-s-subadditive-ergodic-theorem/kingman-ae-general.md)

## Expansion

1. The model: the environmental process, the projection matrices and conditions (i)–(ii), which give demographic weak ergodicity.
2. The general theorem for stationary random matrices with $E \log^+\|X_1\| < \infty$: $\frac1n\log\|X_n \cdots X_1\|$ converges almost surely, to a constant under ergodicity, by subadditivity and Kingman's theorem.
3. Independence of the norm, and the identification of the norm growth rate with the growth rate of every stage under conditions (i)–(ii).
4. Convergence in distribution of the normalized structure, as a separate statement.

## Sources

- D. Steinsaltz, S. Tuljapurkar and C. Horvitz, Derivatives of the stochastic growth rate, Theor. Popul. Biol. 80 (2011), 1–15; Sections 1–2 in the numbering of the arXiv version, arXiv:1002.1424. <https://doi.org/10.1016/j.tpb.2011.03.004>
- Original result: H. Furstenberg and H. Kesten, Products of random matrices, Ann. Math. Statist. 31 (1960), 457–469. <https://doi.org/10.1214/aoms/1177705909> The existence of the stochastic growth rate as the leading Lyapunov exponent follows Steinsaltz, Tuljapurkar and Horvitz.
