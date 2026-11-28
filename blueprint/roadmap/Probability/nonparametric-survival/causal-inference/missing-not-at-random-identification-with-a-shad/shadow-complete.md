# Completeness

Let $\mathcal{Y}$ be a finite set, $\mathcal{Z}$ a set, and $P$ a measure on $\{\mathrm{true}, \mathrm{false}\} \times \mathcal{Y} \times \mathcal{Z}$ with coordinates $R$, $Y$, $Z$; write $p(r, y, z) = P(\{(r, y, z)\})$ as a real number (an infinite point mass counts as $0$). $P$ is complete when for every $g : \mathcal{Y} \to \mathbb{R}$,

$$\Bigl(\forall z \in \mathcal{Z}:\ \sum_{y \in \mathcal{Y}} p(\mathrm{true}, y, z)\, g(y) = 0\Bigr) \implies g = 0.$$

For a finite measure with measurable singletons, equivalently, $\mathbb{E}[g(Y) \mid Z = z, R = \mathrm{true}] = 0$ wherever defined forces $g = 0$.
