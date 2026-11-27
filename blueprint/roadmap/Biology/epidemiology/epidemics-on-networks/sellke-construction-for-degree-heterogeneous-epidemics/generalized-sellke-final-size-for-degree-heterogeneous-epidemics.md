# Generalized Sellke construction and final size of a degree-heterogeneous epidemic

**Model (discrete heterogeneous stochastic epidemic).** A population of $N$ individuals is given. Individual $i$ has an integer *degree* $K_i \sim D$ (probabilities $d_k$), an infectious period $T_i \sim \Gamma$ with values in $[0,\infty)$, and a state $X_i(t) \in \{S, I, R\}$. Each pair $i, j$ makes contacts at the points of a Poisson process of rate $\tau K_i K_j$; a contact between a susceptible and an infective makes the susceptible infective, and an individual infected at time $t$ is removed at time $t + T_i$. All degrees, periods and contact processes are independent.

**Sellke construction.** Give each initially susceptible individual a *resistance* $Q_i \sim \mathrm{Exp}(K_i)$, independent of everything else, and give initial infectives resistance $0$. Define the *infectious pressure*

$$ \Lambda(t) = \tau \int_0^t \sum_{j=1}^N K_j\, \mathbf 1_{\{X_j(u) = I\}}\, du, $$

and let a susceptible become infective at the first time $t$ with $Q_i < \Lambda(t)$.

**Lemma.** The Sellke construction and the epidemic above, with the same $D$, $\Gamma$, $N$, $\tau$ and initial states, are equal in law.

**Theorem (final size).** Let $Z = \lim_{t\to\infty} \sum_{j=1}^N \mathbf 1_{\{X_j(t) = R\}}$ be the final number of removed individuals. Sample degrees, resistances and infectious periods as in the Sellke construction and index individuals so that $Q_1 \le Q_2 \le \dots \le Q_N$ (initial infectives first). Then

$$ Z = \min\Big\{ i \ :\ Q_{i+1} > \tau \sum_{j=1}^{i} K_j T_j \Big\}, $$

with the convention $Q_{N+1} = \infty$.

**Markovian limit.** If $\Gamma = \mathrm{Exp}(\gamma)$ and $m$ initial infectives are chosen uniformly, the counts $S_k, I_k$ of susceptibles and infectives of degree $k$ form a Markov chain with transitions $(S_k, I_k) \to (S_k - 1, I_k + 1)$ at rate $\tau k S_k \sum_l l I_l$ and $I_k \to I_k - 1$ at rate $\gamma I_k$. For a finite degree set and $D$ independent of $N$, with $\beta = \tau N$, the proportions $s_k = \mathbb E[S_k/N]$, $\iota_k = \mathbb E[I_k/N]$ converge as $N \to \infty$ to the solution of

$$ \frac{ds_k}{dt} = -\beta k s_k \sum_l l\, \iota_l, \qquad \frac{d\iota_k}{dt} = \beta k s_k \sum_l l\, \iota_l - \gamma \iota_k, $$

whose disease-free state $(\mathbf d, \mathbf 0)$ is unstable with growth rate $r = \beta\, \mathbb E_D[K^2] - \gamma$ when $r > 0$.

## Expansion

Since $\Pr(Q_i > q) = e^{-K_i q}$, the conditional probability of escaping infection during $[t, t+\delta t]$ given escape up to $t$ is $\exp(-K_i(\Lambda(t+\delta t) - \Lambda(t))) = 1 - \tau K_i \sum_j K_j \mathbf 1_{\{X_j(t)=I\}}\,\delta t + o(\delta t)$, matching the Poisson contact hazard in the original model, which gives the lemma. In the Sellke picture individuals are infected in increasing order of resistance, and the total pressure accumulated by the first $i$ infected individuals over their whole infectious periods is $\tau \sum_{j \le i} K_j T_j$; the epidemic stops at the first $i$ for which the next resistance exceeds this pressure. Evaluating the final size thus needs only sorting and a cumulative sum, which makes large final-size samples cheap and allows heavy-tailed degree laws such as a truncated Zipf law, where the second moment $\mathbb E_D[K^2]$ grows with the truncation point and the reproduction number $\rho = \beta\,\mathbb E_D[K^2]\,\mathbb E_\Gamma[T]$ loses its threshold role at finite size. The ODE limit follows from Kurtz's theorem for density-dependent Markov chains after writing the rates as $N$ times functions of $S_k/N$ and $I_k/N$.

## Sources

- Thomas House, "Non-Markovian stochastic epidemics in extremely heterogeneous populations", arXiv:1403.2878 (2014), Section 2.1 (Definition 1), Section 2.2 (Definition 2, Theorems 1–2, growth rate), Section 2.3 (Definition 3, Lemma 1, Theorem 3). <https://doi.org/10.48550/arXiv.1403.2878>. Published version: Mathematical Modelling of Natural Phenomena 9(2) (2014), 153–160, <https://doi.org/10.1051/mmnp/20149210>; locators above refer to the arXiv version.
