# Coefficient reduction of the general recombination equation

**Setting.** Let $S = \{1,\dots,n\}$ index the sites of a genome, $X = X_1\times\cdots\times X_n$ a product of locally compact spaces of alleles, and $\mathcal M(X)$ the finite measures on $X$. For a partition $\mathcal A = \{A_1,\dots,A_r\}$ of $S$, the **recombinator** is

$$R_{\mathcal A}(\nu) = \frac{1}{\|\nu\|^{r-1}}\bigotimes_{i=1}^{r}\bigl(\pi_{A_i}.\nu\bigr), \qquad R_{\mathcal A}(0) = 0,$$

the product of the marginals of $\nu$ on the blocks of $\mathcal A$ (a type is assembled from independent parents, one per block). Given rates $\varrho(\mathcal A) \ge 0$ for every partition, the **general recombination equation** in continuous time is

$$\dot\omega_t = \sum_{\mathcal A \in \mathbb P(S)} \varrho(\mathcal A)\bigl(R_{\mathcal A} - \mathrm{id}\bigr)(\omega_t).$$

It covers any number of parents and any pattern of crossovers.

**Theorem.**

1. (Recombinator algebra.) On $\mathcal M_+(X)$, $R_{\mathcal A}R_{\mathcal B} = R_{\mathcal A\wedge\mathcal B}$. So recombinators are idempotent and commute, and each is Lipschitz.
2. (Well-posedness.) The Cauchy problem has a unique solution, $\mathcal M_+(X)$ is forward invariant and the flow preserves the norm. In particular probability measures stay probability measures.
3. (Exact finite-dimensional reduction.) $\omega_t$ solves the equation with initial condition $\omega_0 \in \mathcal M_+(X)$ if and only if

$$\omega_t = \sum_{\mathcal B \in \mathbb P(S)} a_t(\mathcal B)\,R_{\mathcal B}(\omega_0),$$

where the probability vector $a_t$ on the $B(n)$ partitions of $S$ ($B(n)$ the Bell number) solves the $\omega_0$-independent nonlinear ODE

$$\dot a_t(\mathcal A) = -\varrho_{\mathrm{tot}}\,a_t(\mathcal A) + \sum_{\mathcal B \succcurlyeq \mathcal A}\gamma(a_t;\mathcal A,\mathcal B)\,\varrho(\mathcal B), \qquad a_0(\mathcal B) = \delta(\mathcal B, \mathbf 1_S),$$

with $\gamma(q;\mathcal A,\mathcal B) = \prod_{i=1}^{|\mathcal B|}\sum_{\mathcal C:\ \mathcal C|_{B_i} = \mathcal A|_{B_i}} q(\mathcal C)$ for probability vectors $q$, and $\mathbf 1_S$ the one-block partition.

4. (When the linear formula is exact.) If the recombinators acted linearly along solutions, the coefficients would be

$$a^{\mathrm{lin}}_t(\mathcal A) = \sum_{\mathcal G \subseteq \mathbb P(S),\ \bigwedge\mathcal G = \mathcal A}\ \prod_{\sigma\in\mathcal G}\bigl(1 - e^{-\varrho(\sigma)t}\bigr)\prod_{\tau\notin\mathcal G}e^{-\varrho(\tau)t}.$$

This gives the true solution for $\mathcal A = \mathbf 1_S$ and for every partition into two blocks one of which is a singleton. For $|S| \le 3$ it gives the true solution for all $\mathcal A$. For larger $S$ the linearity assumption fails in general.

5. (Backward and generic solution.) The marginalized coefficient vectors $a^U_t$ on subsystems $U \subseteq S$ again solve the equation of the same form with induced rates, and $a^U_t(\mathcal A) = \mathbb P(\Sigma^U_t = \mathcal A \mid \Sigma^U_0 = \mathbf 1_U)$ for the partitioning process $\Sigma^U$ of ancestral blocks. When the decay rates $\psi^S(\mathcal A) = \sum_{i}\psi^{A_i}(\mathbf 1_{A_i})$ (built from $\psi^U(\mathbf 1_U) = \sum_{\mathcal A \ne \mathbf 1_U}\varrho^U(\mathcal A)$) are distinct, the solution has the exponential form $a_t(\mathcal A) = \sum_{\mathcal B\succcurlyeq\mathcal A}\theta(\mathcal A,\mathcal B)e^{-\psi(\mathcal B)t}$. Its coefficients $\theta$ are determined recursively from those of smaller subsystems.

## Expansion

Item 1 is a direct computation with marginals. Item 3 follows by substituting the ansatz into the equation and using item 1 to collapse products of recombinators applied to a convex combination of $R_{\mathcal B}(\omega_0)$. Because the coefficient ODE does not involve $\omega_0$, the nonlinear measure-valued problem reduces to a universal finite-dimensional one. Exactness of the linear formula for $|S| \le 3$ holds because every partition of a set of at most three elements is either trivial or has a singleton block. Item 5 is a consistency (marginalization) argument followed by a Markov-chain reading of the coefficient ODE backwards in time.

## Sources

- Ellen Baake, Michael Baake, Majid Salamat, "The general recombination equation in continuous time and its solution", *Discrete and Continuous Dynamical Systems, Series A* 36 (2016), 63–95, <https://doi.org/10.3934/dcds.2016.36.63>; preprint arXiv:1409.1378, <https://doi.org/10.48550/arXiv.1409.1378>. Numbering of the arXiv version: Section 2 (Propositions 1–2), Section 3 (Propositions 3–4, Theorem 1), Section 4 (Proposition 5, Theorem 2, Corollary 2), Section 5 (Propositions 6–7), Section 6 (Theorem 3), Section 7 (Theorem 4).
