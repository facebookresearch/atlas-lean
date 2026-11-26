# Tropical hard-margin support vector machine on tree space

**Setting.** Phylogenetic trees with $N$ labelled leaves, encoded by their dissimilarity maps, are points of the tropical projective torus $\mathbb{R}^e/\mathbb{R}\mathbf{1}$, $e = \binom{N}{2}$, with the tropical metric $d_{\mathrm{tr}}(v, w) = \max_i(v_i - w_i) - \min_i(v_i - w_i)$; equidistant trees form the space of ultrametrics, which is a tropical linear space. Over the max-plus semiring, the **tropical hyperplane** with normal vector $\omega \in \mathbb{R}^e/\mathbb{R}\mathbf{1}$ is

$$
H_\omega = \big\{x : \max\{\omega_1 + x_1, \dots, \omega_e + x_e\} \text{ is attained at least twice}\big\},
$$

and it divides the torus into $e$ open sectors $S^i_\omega = \{x : \omega_i + x_i > \omega_j + x_j \ \forall j \ne i\}$. The tropical distance from $x$ to $H_\omega$ equals the gap between the largest and second-largest coordinates of $x + \omega$.

**Hard-margin problem.** Given two classes $P, Q$ of trees, for instance gene trees from two species-tree hypotheses, a tropical hard-margin SVM seeks a hyperplane such that all points of each class lie in a common open sector (sectors differing between classes), maximizing the smallest distance of a data point to $H_\omega$:

$$
\max_{\omega}\ \min_{\xi \in P \cup Q}\big\{(\xi + \omega)_{i(\xi)} - (\xi + \omega)_{j(\xi)}\big\} \quad\text{s.t.}\quad (\xi + \omega)_l \le (\xi + \omega)_{j(\xi)} \le (\xi + \omega)_{i(\xi)}\ \ \forall \xi,\ \forall l \ne i(\xi), j(\xi),
$$

where $i(\xi)$ and $j(\xi)$ index the largest and second-largest coordinates of $\xi + \omega$.

**Theorem (linear programming formulation).** For a fixed assignment of the indices $i(\xi), j(\xi)$, the normal vector of the tropical hard-margin hyperplane is the optimal solution of the linear program

$$
\begin{aligned}
\max_{z, \omega}\ & z\\
\text{s.t. }\ & z + \xi_{j(\xi)} + \omega_{j(\xi)} - \xi_{i(\xi)} - \omega_{i(\xi)} \le 0 && \forall \xi \in P \cup Q,\\
& \omega_{j(\xi)} - \omega_{i(\xi)} \le \xi_{i(\xi)} - \xi_{j(\xi)} && \forall \xi \in P \cup Q,\\
& \omega_l - \omega_{j(\xi)} \le \xi_{j(\xi)} - \xi_l && \forall \xi \in P \cup Q,\ \forall l \ne i(\xi), j(\xi),
\end{aligned}
$$

and the optimal value $z$ is the tropical margin.

## Expansion

Tree space is not Euclidean, so classical SVMs on vectorized trees ignore its geometry. In the tropical torus, hyperplanes are polyhedral fans, and the distance from a point to $H_\omega$ in $d_{\mathrm{tr}}$ is the amount by which the maximal coordinate of $x + \omega$ must drop to tie with the runner-up. Once the sector of each data point is fixed (via the choice of $i(\xi), j(\xi)$), all constraints and the distance become linear in $\omega$. Introducing an epigraph variable $z$ for the minimum turns the max-min problem into a single linear program. The second and third families of constraints encode that $i(\xi)$ and $j(\xi)$ really are the top two coordinates. Enumerating or searching over admissible index assignments, together with soft-margin relaxations, gives classifiers whose decision regions are tropical sectors. Restricted to ultrametrics, these sectors are unions of cells where trees share combinatorial features.

## Sources

- Ruriko Yoshida, "Tropical Data Science", arXiv (2020), Section 4 (tropical arithmetic and the tropical metric, Definition 15), Section 6 (tropical hyperplanes and sectors, Definitions 30–33, Theorem 34), <https://doi.org/10.48550/arXiv.2005.06586>.
- Xiaoxian Tang, Houjie Wang and Ruriko Yoshida, "Tropical support vector machine and its applications to phylogenomics" (2020), the original source of the linear programming formulation.
- Bernd Gärtner and Martin Jaggi, "Tropical support vector machines", technical report (2006).
