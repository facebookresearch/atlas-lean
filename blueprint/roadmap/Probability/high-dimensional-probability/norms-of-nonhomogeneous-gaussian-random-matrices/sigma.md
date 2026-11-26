# Matrix variance parameter $\sigma$ of a Gaussian series

Let $d, n \in \mathbb{N}$ and let $A_1, \dots, A_n$ be real $d \times d$ matrices. Then

$$\sigma = \Big\| \sum_{k=1}^n A_k^2 \Big\|^{1/2},$$

where $\|\cdot\|$ is the spectral norm, the operator norm on $\mathbb{R}^d$ with the Euclidean norm. For symmetric matrices $A_k$, $\sum_k A_k^2 = \mathbb{E}\big[X^2\big]$ for the Gaussian series $X = \sum_k g_k A_k$ with independent standard Gaussian $g_k$, so $\sigma$ is its matrix variance parameter (Bandeira, equation (36); Proposition 4.16 recalls it beside the weak variance $\sigma_*$ of Definition 4.15). For nonsymmetric matrices the formula is still defined but is not that variance: for the single coefficient $A = E_{12}$, $A^2 = 0$ while $\mathbb{E}[(gA)(gA)^{\mathsf T}] = E_{11}$.
