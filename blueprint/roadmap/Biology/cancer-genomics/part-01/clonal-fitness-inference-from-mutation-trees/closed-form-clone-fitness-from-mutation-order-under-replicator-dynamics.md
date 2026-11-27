# Closed-form clone fitness from mutation order under replicator dynamics

**Model.** A tumour mutation tree $T$ has nodes $0, 1, \dots, n$, where $0$ is the normal clone and node $i \ge 1$ is created from its parent $p_i$ by a mutation at time $t_i$. Between mutation events the relative clone abundances $x = (x_0, \dots, x_n)$ follow the [replicator equation](../../../population-dynamics/replicator-dynamics/is-solution.md) with constant fitnesses,

$$\dot x_k = f_k x_k - x_k \sum_{l} f_l x_l,$$

and at time $t_i$ a fraction $\varepsilon \ll 1$ of clone $p_i$ becomes clone $i$. Cells are sampled at time $t_{n+1}$ with observed clone counts $a_0, \dots, a_n$ (multinomial given $x(t_{n+1})$). Waiting times between consecutive events have mean $1/\theta$, where the mutation rates have mean $\theta$; the normal clone has fitness $f_0 = 1$.

**Two-clone reduction.** For any two clones $i, j$, the relative abundance $y_i = x_i / (x_i + x_j)$ again obeys a two-type replicator equation, so if $y_i = \varepsilon$ at time $0$,

$$y_i(t) = \frac{\varepsilon e^{f_i t}}{(1 - \varepsilon) e^{f_j t} + \varepsilon e^{f_i t}}.$$

**Proposition.** Fix an order $\mu$ of the mutation events compatible with $T$ (ancestors first), with $\mu_i$ the position of event $i$. Ignoring the discontinuities caused by later births, the times, rates and fitnesses maximizing the product of the time, rate and abundance likelihoods are

$$\theta_i = \theta, \qquad t_i = \frac{\mu_i - 1}{\theta}, \qquad t_{n+1} = \frac{n}{\theta},$$

$$f_i = 1 - \theta \sum_{j \in A_i \setminus \{0\}} \frac{1}{n - \mu_j + 1} \log\!\left(\frac{\varepsilon}{1 - \varepsilon} \cdot \frac{a_{p_j}}{a_j}\right), \qquad i = 1, \dots, n,$$

where $A_i$ is the set of ancestors of $i$ including $i$. Maximum-likelihood inference of clonal selection then reduces to a discrete search over orders $\mu$ maximizing the remaining mutation likelihood $\sum_j \log x_{p_j}(t_j)$, a single-machine scheduling problem with precedence constraints given by $T$.

## Depends on

- [Solution of the replicator equation](../../../population-dynamics/replicator-dynamics/is-solution.md)

## Expansion

The time and rate factors are maximized at their means: consecutive events spaced by $1/\theta$, all rates equal to $\theta$. The multinomial factor is maximized when $x_i(t_{n+1}) = a_i / \sum_l a_l$, which implies $y_i(t_{n+1}) = a_i / (a_i + a_{p_i})$ for each clone and its parent. Inserting the two-clone solution with elapsed time $t_{n+1} - t_i = (n - \mu_i + 1)/\theta$ gives

$$f_{p_i} - f_i = \frac{\theta}{n - \mu_i + 1} \log\!\left(\frac{\varepsilon}{1 - \varepsilon} \cdot \frac{a_{p_i}}{a_i}\right),$$

and summing these differences along the path from the root, with $f_0 = 1$, gives the formula. The two-clone reduction holds because $\dot y_i = y_i (1 - y_i)(f_i - f_j)$ depends only on $f_i - f_j$.

## Sources

- P. Skums, V. Tsyvina and A. Zelikovsky, "Inference of clonal selection in cancer populations using single-cell sequencing data", Bioinformatics 35 (2019), i398–i407, Eqs. (2)–(13) and Proposition 1. <https://doi.org/10.1093/bioinformatics/btz392> PMCID: PMC6612866.
