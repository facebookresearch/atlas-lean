# Simplicial contagion model and its mean-field equation

Let $\mathcal{K}$ be a simplicial complex on $N$ vertices: a family of simplices (subsets of vertices) closed under taking subsets, an $\omega$-simplex having $\omega + 1$ vertices. Each vertex $i$ carries a state $x_i(t) \in \{0, 1\}$ (susceptible or infectious). The **simplicial contagion model of order $D$** ($1 \le D \le N - 1$) has infection probabilities $\beta_1, \dots, \beta_D \in [0, 1]$ and a recovery probability $\mu \in (0, 1]$ per unit time:

- for every $\omega$-simplex $\sigma$ with $1 \le \omega \le D$ containing a susceptible vertex $i$ whose other $\omega$ vertices are all infectious, $i$ becomes infectious through $\sigma$ with probability $\beta_\omega$ (the process $\mathrm{Simp}(S, \omega I) \to \mathrm{Simp}((\omega + 1) I)$);
- every infectious vertex recovers with probability $\mu$ (the process $I \to S$).

Because all faces of a simplex belong to $\mathcal{K}$, a simplex in which only $p < \omega$ of the other vertices are infectious still transmits through its $p$-dimensional faces. For $D = 1$ only links transmit and the model is the SIS model on the graph of 1-simplices; for $D = 2$ one writes $\beta = \beta_1$ and $\beta_\Delta = \beta_2$.

**Mean-field equation.** Let $k_\omega(i)$ be the generalized degree of vertex $i$ (the number of $\omega$-simplices containing $i$) and $\langle k_\omega \rangle$ its average. Under homogeneous mixing, with the states of distinct vertices treated as independent, the density of infectious vertices $\rho(t) = \frac{1}{N} \sum_i x_i(t)$ obeys

$$\frac{d\rho}{dt} = -\mu \rho + \sum_{\omega = 1}^{D} \beta_\omega \langle k_\omega \rangle \, \rho^{\omega} (1 - \rho) .$$

For $D = 1$ this is the SIS mean-field equation, with steady states $\rho^* = 0$ and $\rho^* = 1 - \mu / (\beta \langle k_1 \rangle)$ and a continuous transition at $\beta \langle k_1 \rangle / \mu = 1$.

## Depends on

- [Solution of the SIS system](../../sis-epidemic-model/is-solution.md)

## Expansion

A susceptible vertex receives infection through an $\omega$-simplex only when all $\omega$ co-members are infectious, which under independence has probability $\rho^\omega$; there are on average $\langle k_\omega \rangle$ such simplices, and the susceptible fraction is $1 - \rho$. Summing these gain terms over $\omega$ and subtracting recoveries gives the equation. The interaction order $\omega$ thus appears as the power $\rho^\omega$: higher-order channels are negligible when few vertices are infectious but grow faster than the pairwise channel as $\rho$ increases, which is the origin of the discontinuous behaviour analysed for $D = 2$. On empirical face-to-face contact complexes and on random simplicial complexes with peaked generalized degree distributions, simulations with rescaled infectivities $\lambda = \beta \langle k \rangle / \mu$, $\lambda_\Delta = \beta_\Delta \langle k_\Delta \rangle / \mu$ agree with this mean-field picture.

## Sources

- I. Iacopini, G. Petri, A. Barrat and V. Latora, "Simplicial models of social contagion", Nature Communications 10 (2019), Results ("The contagion model", "Mean field approach"), Eq. (1), <https://doi.org/10.1038/s41467-019-10431-6> (PMC6554271).
