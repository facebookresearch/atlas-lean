# Generating function and closed form of the coefficients $\alpha_k$

Let $\alpha_k \in \mathbb{Q}$ be given by $\alpha_0 = 1$, $\alpha_1 = 0$ and
$\alpha_{k+2} = -\alpha_{k+1} - \alpha_k / 2$. Then, as formal power series over $\mathbb{Q}$,

$$\Bigl(\sum_{k \ge 0} \alpha_k z^k\Bigr) (2 + 2z + z^2) = 2 + 2z,$$

so $\sum_k \alpha_k z^k = (2 + 2z)/(2 + 2z + z^2)$, and for every $k \ge 0$

$$\alpha_k = \frac{k + 1}{2^k} \sum_{\ell=0}^{k} \frac{(-1)^\ell\, 2^\ell}{\ell + 1} \binom{\ell + 1}{k - \ell}.$$

## Sources

- Nouara Mokhtari, Rachid Boumahdi, and Farid Bencherif, "Generalizations of Several Explicit Formulas for Euler Polynomials", INTEGERS 25 (2025), Article A65, Lemma 2.2.
