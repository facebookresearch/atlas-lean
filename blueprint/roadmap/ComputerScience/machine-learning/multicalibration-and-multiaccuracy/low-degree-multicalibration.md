# Low-degree multicalibration

Let $D$ be a distribution over $X \times \{0,1\}$ with Bayes predictor $p^*(x) = \mathbb{E}[y \mid x]$, let $p : X \to [0,1]$ be a predictor, and let $\mathcal{C}$ be a collection of functions $c : X \to [0,1]$ (indicators of subpopulations being the main example). For a class $W$ of weight functions $w : [0,1] \to [0,1]$, the predictor $p$ is **$(\mathcal{C}, W, \alpha)$-multicalibrated** if

$$
\big| \mathbb{E}\big[c(x)\, w(p(x))\, (y - p(x))\big] \big| \le \alpha \quad \text{for all } c \in \mathcal{C} \text{ and } w \in W .
$$

For $k \ge 1$, $p$ is **degree-$k$ $\alpha$-multicalibrated** if this holds for the class $W_k$ of polynomials $w(z) = \sum_{j < k} q_j z^j$ of degree at most $k - 1$ with $w(z) \in [0,1]$ for all $z \in [0,1]$ and $\sum_j |q_j| \le 1$. Degree $1$ is multiaccuracy (the constant weight $w = 1$), and degree $2$ adds the constraints $|\mathbb{E}[c(x)\,p(x)\,(y - p(x))]| \le \alpha$. The notions get stronger with $k$, and they are relaxations of smooth multicalibration (all $1$-Lipschitz weights) and of full multicalibration (indicators of the intervals $[(j-1)\delta, j\delta)$, $j = 1, \dots, 1/\delta$, of a $\delta$-grid with $1/\delta$ an integer, the last one closed as $[1 - \delta, 1]$ so that the prediction $p = 1$ is covered): every $\alpha$-smoothly multicalibrated predictor is degree-$k$ $k\alpha$-multicalibrated. For $\ell$ classes, predictions lie in the simplex $\Delta_\ell$, the weights are vectors of such polynomials in $\ell$ variables, and the constraint is $|\mathbb{E}[c(x)\langle w(p(x)), y - p(x)\rangle]| \le \alpha$ with $y$ the one-hot label.

## Depends on

- [Multicalibrated predictors](multicalibrated-predictor.md)

## Sources

- P. Gopalan, M. P. Kim, M. Singhal, S. Zhao, "Low-Degree Multicalibration", COLT (2022), arXiv:2203.01255, Definitions 3.1, 3.2, 3.4 and 3.6, Proposition 1.
