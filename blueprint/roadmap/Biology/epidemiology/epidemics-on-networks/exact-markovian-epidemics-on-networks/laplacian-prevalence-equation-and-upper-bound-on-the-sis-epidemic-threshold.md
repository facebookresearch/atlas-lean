# Laplacian prevalence equation and upper bound on the SIS epidemic threshold

**Model.** On a graph $G$ with $N$ nodes, adjacency matrix $A = (a_{kj})$, degrees $d_1, \dots, d_N$, link set $\mathcal{L}$ and Laplacian $Q = \Delta - A$ with $\Delta = \mathrm{diag}(d_1, \dots, d_N)$, run the Markovian SIR process: each infected node infects each susceptible neighbour at rate $\beta$ and is removed at rate $\delta$. The SIS process is the same except that cured nodes become susceptible again. Let $\tau = \beta/\delta$ be the effective infection rate and $t^* = \delta t$ the rescaled time. With $Y_j \in \{S, I, R\}$ the state of node $j$, the exact SIR equations are

$$
\frac{d\Pr[Y_j = I]}{dt} = \mathbb{E}\Big[-\delta 1_{\{Y_j = I\}} + 1_{\{Y_j = S\}}\,\beta\sum_{k=1}^Na_{kj}1_{\{Y_k = I\}}\Big], \qquad \frac{d\Pr[Y_j = R]}{dt} = \delta\Pr[Y_j = I],
$$

and the SIS equation has the same form with $1_{\{X_j = S\}} = 1 - 1_{\{X_j = I\}}$.

**Theorem 1 (prevalence as a Laplacian quadratic form).** Let $w_I = (1_{\{Y_1=I\}}, \dots, 1_{\{Y_N=I\}})$, define $w_R$ similarly, and let $y_I = \frac1N\sum_j\Pr[Y_j = I]$ be the average fraction of infected nodes. For SIR,

$$
\frac{dy_I}{dt^*} = -y_I + \frac{\tau}{N}\,\mathbb{E}\left[w_I^{T}Qw_I - w_I^{T}Aw_R\right],
$$

and for SIS, writing tildes for the SIS quantities,

$$
\frac{d\tilde y_I}{dt^*} = -\tilde y_I + \frac{\tau}{N}\,\mathbb{E}\left[\tilde w_I^{T}Q\tilde w_I\right].
$$

Since $w^{T}Qw = \sum_{(k,l)\in\mathcal{L}}(w_k - w_l)^2$ counts the links joining an infected node to a non-infected node, the prevalence is driven only by infected–uninfected links. At the maximum of $y_I$ (or in the SIS metastable state) the derivative vanishes, so the maximal prevalence is $\frac{\tau}{N}$ times the expected number of such links. For a $d$-regular graph this reduces to an explicit expression in the spectral radius.

**Theorem 2 (upper bound on the SIS threshold).** Let

$$
\varepsilon_G = \lim_{\tilde y_I\downarrow0}\max_{(k,l)\in\mathcal{L}}\Pr[X_k = I \mid X_l = I]
$$

be the largest conditional infection probability across a link at the onset of infection. Then the SIS epidemic threshold satisfies

$$
\tau_c \le \frac{1}{d_{\min}(1 - \varepsilon_G)}.
$$

Since $\varepsilon_G \le \varepsilon_{K_N} = O(N^{-1/2})$ (the complete graph maximises the onset correlation), for large $N$ every graph satisfies $\tau_c \le \frac{1}{d_{\min}}\left(1 + O(N^{-1/2})\right)$.

Together with the general lower bound $\tau_c \ge 1/\lambda_1$, where $\lambda_1$ is the spectral radius of $A$ (equal to the first-order mean-field threshold), this brackets the exact threshold. The bracket is tight for regular graphs and loose for broad degree distributions.

## Depends on

- [Spectral radius and die-out of SIS epidemics on graphs](../../sis-extinction-times-on-finite-graphs/prob-ne-empty-le.md)
- [SIS epidemic model](../../sis-epidemic-model/README.md)

## Expansion

Summing the node equations over $j$ and splitting $\Pr[Y_j = S, Y_k = I] = \Pr[Y_k = I] - \Pr[Y_j = I, Y_k = I] - \Pr[Y_j = R, Y_k = I]$, the three contributions become $\mathbb{E}[w_I^{T}\Delta w_I]$ (each infected node counted with its degree), $-\mathbb{E}[w_I^{T}Aw_I]$ and $-\mathbb{E}[w_I^{T}Aw_R]$. Combining the first two with $\Delta - A = Q$ gives Theorem 1. For Theorem 2, set $d\tilde y_I/dt^* = 0$ in the SIS identity, which gives $\tau^{-1} = \mathbb{E}[\tilde w_I^{T}Q\tilde w_I]/(N\tilde y_I)$. The Laplacian property $w^{T}Qw = \sum_{l\in\mathcal{L}}(w_{l^+} - w_{l^-})^2$ turns the numerator into $\sum_i\Pr[X_i = I]\sum_ja_{ij}\Pr[X_j = S \mid X_i = I]$. The mediant inequality $\min_k a_k/q_k \le \sum a_k/\sum q_k$ then gives $\tau^{-1} \ge \min_i\sum_ja_{ij}\Pr[X_j = S \mid X_i = I] \ge d_{\min}\min_{(k,l)\in\mathcal{L}}\Pr[X_k = S \mid X_l = I]$. Letting the prevalence tend to $0$ (the threshold regime) turns the last factor into $1 - \varepsilon_G$, and inverting gives the bound.

## Sources

- Piet Van Mieghem, "Exact Markovian SIR and SIS epidemics on networks and an upper bound for the epidemic threshold", arXiv:1402.1731 (2014), Section 2 (governing equations), Section 4 (lower bound, Theorem 1 and Theorem 2), Appendix (proofs of Theorems 1–2), <https://doi.org/10.48550/arXiv.1402.1731>. Published version: Piet Van Mieghem, Faryad Darabi Sahneh, Caterina Scoglio, "An upper bound for the epidemic threshold in exact Markovian SIR and SIS epidemics on networks", 53rd IEEE Conference on Decision and Control (CDC 2014), 6228–6233, <https://doi.org/10.1109/CDC.2014.7040365>; locators above refer to the arXiv version.
