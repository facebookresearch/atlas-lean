# Limiting Simpson index of malignant clones under two mutation orders

**Model.** A continuous-time multitype branching process starts from one wild-type cell, type $s_\emptyset$. Types $s_1,s_2$ carry one driver mutation and $s_{12},s_{21}$ are malignant cells carrying both, indexed by the order of acquisition. A type-$x$ cell divides at rate $a_x$ and dies at rate $b_x$, with net growth $\lambda_x=a_x-b_x$; at division it mutates $s_i\to s_j$ at rate $\mu_{i,j}$ along the admissible pathways $s_\emptyset\to s_1\to s_{12}$ and $s_\emptyset\to s_2\to s_{21}$. Each transformation event founds a malignant clone; with clone sizes $X_i(t)$ (pathway $(1,2)$) and $Y_j(t)$ (pathway $(2,1)$), the Simpson index is
$$R_t=\frac{\sum_iX_i(t)^2+\sum_jY_j(t)^2}{(Z_{12}(t)+Z_{21}(t))^2},$$
the probability that two malignant cells sampled with replacement belong to the same clone.

**Successive exponential approximation.** Conditional on survival, the wild type is replaced by $V_0e^{\lambda_{s_\emptyset}t}$ with $V_0$ exponential of rate $\lambda_{s_\emptyset}/a_{s_\emptyset}$; it founds mutant lineages at Poisson times, and each mutant population is in turn replaced by its long-time exponential amplitude.

**Proposition (single pathway).** If only $s_\emptyset\to s_1\to s_{12}$ is allowed and $0<\lambda_{s_\emptyset}<\lambda_{s_1}<\lambda_{s_{12}}$, then
$$\lim_{t\to\infty}\mathbb E[R_t]=1-\frac{\lambda_{s_1}}{\lambda_{s_{12}}}.$$

**Theorem (two pathways, equal malignant fitness).** Let $\lambda_{s_{12}}=\lambda_{s_{21}}=\lambda$, with growth increasing along each pathway. For an admissible mutation $s_i\to s_j$ with $\lambda_{s_i}<\lambda_{s_j}$ set
$$H_{i,j}=\frac1{a_{s_j}}\Big(\frac{a_{s_j}}{\lambda_{s_j}}\Big)^{\lambda_{s_i}/\lambda_{s_j}}\frac{\pi}{\sin(\pi\lambda_{s_i}/\lambda_{s_j})},$$
$$A_{12}=\mu_{\emptyset,1}H_{\emptyset,1}\big(\mu_{1,12}H_{1,12}\big)^{\lambda_{s_\emptyset}/\lambda_{s_1}},\qquad A_{21}=\mu_{\emptyset,2}H_{\emptyset,2}\big(\mu_{2,21}H_{2,21}\big)^{\lambda_{s_\emptyset}/\lambda_{s_2}}.$$
Then
$$\lim_{t\to\infty}\mathbb E[R_t]=\frac{A_{12}\big(1-\lambda_{s_1}/\lambda\big)+A_{21}\big(1-\lambda_{s_2}/\lambda\big)}{A_{12}+A_{21}},$$
an average of the single-pathway limits weighted by the pathways' effective founding intensities.

## Expansion

In the single-pathway case malignant clones are founded at the times of a Poisson process with exponentially growing intensity $\propto e^{\lambda_{s_1}t}$, and each grows like $e^{\lambda_{s_{12}}(t-\text{founding time})}$ times an exponential amplitude. Clone sizes then form a Poisson point process with power-law intensity of exponent $1+\lambda_{s_1}/\lambda_{s_{12}}$, whose normalized sizes follow a Poisson–Dirichlet law with parameter $\lambda_{s_1}/\lambda_{s_{12}}$, for which the expected sum of squared proportions is $1-\lambda_{s_1}/\lambda_{s_{12}}$. With two pathways and equal malignant growth, each pathway's total contributes in proportion to its random amplitude; the constants $H_{i,j}$ come from the long-time amplitude of the lineages founded by an exponentially growing parent population, and $A_{12},A_{21}$ compose them along each pathway.

## Sources

- Y. Chu, X. Sheng, X. Zhang, Z. Wang, "Mutation Order and Selection Shape Intratumor Heterogeneity in Tumor Evolution", arXiv:2609.25838 (2026), Section 3 (model, Simpson index), Section 4 (successive exponential approximation, Proposition 1, Theorem 1), <https://doi.org/10.48550/arXiv.2609.25838>.
