# Moment generating function of the frequency spectrum of a Gibbs-type partition

**Setting.** For a random partition of $\{1, \dots, n\}$ let $M_{jn}$ be the number of blocks of size $j$ and $K_n = \sum_{j=1}^n M_{jn}$ the number of blocks, so $\mathbf{M}_n = (M_{1n}, \dots, M_{nn})$ satisfies $\sum_j j M_{jn} = n$. The partition is **Gibbs-type** if

$$\mathbb{P}(\mathbf{M}_n = \mathbf{m},\ K_n = k) = C_{nk} \prod_{j=1}^n \frac{q_j^{m_j}}{m_j!}, \qquad \mathbf{m} \in A_{kn} = \Big\{ m_j \ge 0 : \sum_j m_j = k,\ \sum_j j m_j = n \Big\},$$

with weights $q_j > 0$ and normalizing constants $C_{nk} > 0$. Put $q_{jn} = q_j / \sum_{\ell \le n} q_\ell$ and $\mathbf{q}_n = (q_{1n}, \dots, q_{nn})$.

**Theorem.** For every $\nu \in \mathbb{R}$, $\mathbf{u}_n \in \mathbb{R}^n$ and $k \in \{1, \dots, n\}$,

$$\mathbb{E}\Big( e^{\nu \mathbf{u}_n^{\mathsf T}(\mathbf{M}_n / K_n - \mathbf{q}_n)};\ K_n = k \Big) = \mathbb{E}\Big( e^{\frac{\nu}{k}\sum_{i=1}^k (V_i - \mathbb{E} V_i)} \Big) \cdot \frac{\mathbb{P}\big(\sum_{i=1}^k \widehat X_i^{(\nu \mathbf{u}_n)} = n\big)}{\mathbb{P}\big(\sum_{i=1}^k \widehat X_i^{(0)} = n\big)} \cdot \mathbb{P}(K_n = k),$$

where $V_1, \dots, V_k$ are i.i.d. with $\mathbb{P}(V_1 = u_{jn}) = q_{jn}$ (so $\mathbb{E} V_1 = \mathbf{u}_n^{\mathsf T}\mathbf{q}_n$ and $\operatorname{Var} V_1 = \mathbf{u}_n^{\mathsf T} \mathbf{Q}_n \mathbf{u}_n$ with $\mathbf{Q}_n = \operatorname{diag}(\mathbf{q}_n) - \mathbf{q}_n \mathbf{q}_n^{\mathsf T}$), the $\widehat X_i^{(\nu \mathbf{u}_n)}$ are i.i.d. on $\{1, \dots, n\}$ with tilted law

$$\mathbb{P}\big(\widehat X_1^{(\nu \mathbf{u}_n)} = j\big) = \frac{q_j\, e^{\nu u_{jn}/k}}{\sum_{\ell=1}^n q_\ell\, e^{\nu u_{\ell n}/k}},$$

and $\widehat X_i^{(0)}$ have law $\mathbf{q}_n$. Both conditioning probabilities are positive for $1 \le k \le n$.

## Depends on

- [Ewens sampling formula](../ewens-sampling-formula-and-the-chinese-restauran/ewens-prob.md)

## Expansion

The Gibbs form makes $\mathbf{M}_n$ given $K_n = k$ the occupation counts of $k$ i.i.d. block sizes $\widehat X_1^{(0)}, \dots, \widehat X_k^{(0)}$ with law $\mathbf{q}_n$, conditioned on $\sum_i \widehat X_i^{(0)} = n$ (the multinomial identity $\sum_{\mathbf{m} \in A_{kn}} \prod_j \mu_j^{m_j}/m_j! = \frac{\mu_+^k}{k!}\,\mathbb{P}(\sum_{i \le k} X_i = n)$ for i.i.d. $X_i$ with law $\mu_j/\mu_+$). Multiplying the summand by $e^{\nu \mathbf{u}_n^{\mathsf T}\mathbf{m}/k}$ is an exponential tilt of the block-size law; the normalizer of the tilt is the mgf of $V_1$, and the conditioning on the total produces the ratio of local probabilities. The formula reduces asymptotics of $\mathbf{M}_n$ to triangular arrays of i.i.d. variables plus a local limit theorem for their sums. The Ewens sampling formula is the case $q_j = 1/j$.

## Sources

- Ross Arthur Maller, Soudabeh Shemehsavar, "Limit Theorems for the Pitman-Yor Frequency Spectrum", arXiv (2026). Theorem 2.1 and Lemma 5.1. <https://doi.org/10.48550/arXiv.2607.23401>
