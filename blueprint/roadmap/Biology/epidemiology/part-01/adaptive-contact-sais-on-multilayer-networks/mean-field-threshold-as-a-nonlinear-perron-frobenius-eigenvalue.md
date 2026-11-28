# Mean-field threshold of adaptive-contact SAIS as a nonlinear Perron–Frobenius eigenvalue

**Model (AC-SAIS).** $N$ individuals are each susceptible (S), alert (A) or infected (I). Two nonnegative weighted adjacency matrices on the same node set, possibly asymmetric, describe contacts: $W_S = [w^S_{ij}]$ for a node while it is susceptible and $W_A = [w^A_{ij}]$ for a node while it is alert ($w_{ij} > 0$ means $j$ can act on $i$). The continuous-time Markov transitions are: S $\to$ I at rate $\beta \sum_j w^S_{ij}\,\mathbf 1\{j \in I\}$; S $\to$ A at rate $\kappa \sum_j w^S_{ij}\,\mathbf 1\{j \in I\}$; A $\to$ I at rate $\beta \sum_j w^A_{ij}\,\mathbf 1\{j \in I\}$; I $\to$ S at rate $\delta$. The switching contact network is thus a static two-layer network. Its first-order mean-field approximation for $p_i = \Pr(i \in I)$ and $q_i = \Pr(i \in A)$ is

$$\dot p_i = -\delta p_i + \beta(1 - q_i - p_i)\sum_j w^S_{ij} p_j + \beta q_i \sum_j w^A_{ij} p_j,$$

$$\dot q_i = \kappa(1 - q_i - p_i)\sum_j w^S_{ij} p_j - \beta q_i \sum_j w^A_{ij} p_j.$$

Assume $\beta, \delta > 0$ and $\kappa \ge 0$, and write $\tau = \beta/\delta$ (effective infection rate) and $\bar\kappa = \kappa/\beta$ (relative alerting rate).

**M-connectivity.** Let $\boldsymbol G^1$ be the directed graph on singletons with a link $j \to i$ when $w^S_{ij} > 0$ and $w^A_{ij} > 0$. Given $\boldsymbol G^k$, let $\boldsymbol G^{k+1}$ have the strongly connected components of $\boldsymbol G^k$ as hypernodes, with a link $J \to I$ when some $i \in I$ has $w^S_{ij_1} > 0$ and $w^A_{ij_2} > 0$ for some $j_1, j_2 \in J$. The two-layer network is *M-connected* if some $\boldsymbol G^{k}$ is strongly connected. Strong connectivity of the intersection graph is sufficient; strong connectivity of both layers is necessary.

**Theorem.** Assume the two-layer network is M-connected.

1. Every equilibrium of the mean-field system has either $p^*_i = 0$ for all $i$ or $p^*_i > 0$ for all $i$, and a positive equilibrium satisfies

    $$\frac{p^*_i}{1 - p^*_i} = \tau\,\frac{(\bar\kappa + 1)\sum_j w^A_{ij}p^*_j \sum_j w^S_{ij}p^*_j}{\bar\kappa \sum_j w^S_{ij}p^*_j + \sum_j w^A_{ij}p^*_j}.$$

2. Define the map $F$ on the nonnegative cone by

    $$F(z)_i = \frac{\sum_j w^A_{ij} z_j \,\sum_j w^S_{ij} z_j}{\bar\kappa \sum_j w^S_{ij} z_j + \sum_j w^A_{ij} z_j}$$

    for $\bar\kappa > 0$ (with $F(z)_i = 0$ when both sums vanish, the only case in which the denominator vanishes), and set $F(z) = W_S z$ for $\bar\kappa = 0$. $F$ is positively homogeneous of degree one and concave, and the nonlinear eigenproblem $F(z) = \mu z$ has a unique solution $z_* \succ 0$ with $\|z_*\|_2 = 1$, with eigenvalue $\mu_* > 0$.

3. The mean-field epidemic threshold, the value $\tau_c$ at which a positive endemic equilibrium bifurcates from the disease-free one, is characterized by $z = \tau_c(\bar\kappa + 1) F(z)$ having a solution $z \succ 0$, so

    $$\tau_c = \frac{1}{(\bar\kappa + 1)\,\mu_*}.$$

4. For any $c > 0$ and $z_0 \succ 0$ with $\|z_0\|_2 = 1$, the iteration $z_{k+1} = (F(z_k) + c z_k)/\|F(z_k) + c z_k\|_2$ converges to $z_*$.

At $\bar\kappa = 0$, $F(z) = W_S z$ and $\tau_c = 1/\lambda_1(W_S)$, the mean-field SIS threshold on the default layer; as $\bar\kappa \to \infty$, $\tau_c \to 1/\lambda_1(W_A)$.

## Expansion

Setting $\dot q_i = 0$ expresses $q^*_i$ through the infected neighborhood sums; substituting into $\dot p_i = 0$ gives the equilibrium relation in part 1. Positivity spreads from one positive node along links of $\boldsymbol G^1$, then from component to component along links of $\boldsymbol G^2, \boldsymbol G^3, \dots$, which is where M-connectivity enters. Dividing the equilibrium relation by $\sum_j w^S_{ij}p^*_j$ and letting $\tau \downarrow \tau_c$ (so $p^* \to 0$), L'Hôpital's rule with $z_i = dp^*_i/d\tau$ at $\tau_c$ gives the nonlinear eigenproblem in part 3, a second-order transition. Homogeneity and concavity of $F$ follow from those of $g(u,v) = uv/(u+v)$ composed with linear maps; M-connectivity is equivalent to the primitivity-type condition (the source's condition C2) under which a nonlinear Perron–Frobenius theorem for homogeneous concave maps gives existence, uniqueness and strict positivity of the eigenvector and convergence of the shifted power iteration. The threshold is that of the mean-field model, a lower bound for the threshold of the exact stochastic process.

## Sources

- F. D. Sahneh, A. Vajdi, J. Melander and C. M. Scoglio, "Contact adaption during epidemics: a multilayer network formulation approach", *IEEE Transactions on Network Science and Engineering* (2019), Sections 3.2, 4.2–4.4 and 5.1: Definition 5, Eqs. (2)–(4) and (8)–(10), Lemma 4, Lemma 5, Theorem 4, Theorem 6 and Corollary 1. <https://doi.org/10.1109/tnse.2017.2770091> (PMC7309295)
