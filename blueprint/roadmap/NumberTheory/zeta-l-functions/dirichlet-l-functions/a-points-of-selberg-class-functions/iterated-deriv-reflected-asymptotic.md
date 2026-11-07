# Asymptotics of the derivatives of the reflected function (Lemma 2)

Let $F$ be a function
in the Selberg class with Gamma-factor data $\lambda_j$, $\mu_j$ for $1 \le j \le r$, conductor
$Q$, root number $\omega$ and degree $d_F = 2 \sum_j \lambda_j$, let $k \ge 1$ and let $c > 1$.
Write $\log$ for the principal branch of the logarithm and put

$$M(s) = \frac{d_F^k}{\pi^r \omega} Q^{2s - 1}
\prod_{j=1}^r \Gamma(\lambda_j s + \mu_j) \Gamma(\lambda_j s + 1 - \lambda_j - \bar\mu_j)
\prod_{j=1}^r \sin\bigl(\pi (\lambda_j + \bar\mu_j - \lambda_j s)\bigr) (\log s)^k F(s).$$

Let $G(w) = \overline{F(1 - \bar w)}$ and let $G^{(k)}$ be its $k$-th derivative. Then there are
real numbers $\tau$ and $C$ such that $|G^{(k)}(s) - M(s)| \le C |M(s)| / |\log s|$ for every
$s \in \mathbb{C}$ with $\operatorname{Re} s > c$ and $|\operatorname{Im} s| \ge \tau$.

## Sources

- M. P. Chaudhary, Salem Guiben, Kamel Mazhouda and Mohammed Mekkaoui, *On the a-Points of the kth Derivative of an L-Function in the Selberg Class*, INTEGERS 24 (2024), Article A11, Lemma 2 (`integers-2024-A11-lem-2`).
