# Measure Real eq sum fiber

Let $\mathcal{Y}$ and $\mathcal{Z}$ be finite sets with measurable singletons, and let $P$ be a finite measure on $\{\mathrm{true}, \mathrm{false}\} \times \mathcal{Y} \times \mathcal{Z}$, whose coordinates are the response indicator $R$, the outcome $Y$ and the shadow variable $Z$. Write $p(r, y, z) = P(\{(r, y, z)\})$ for the point masses.

If $s \subseteq \{(r, y', z) : y' = y\}$ for some outcome value $y$, then

$$P(s) = \sum_{z \in \mathcal{Z}} \Bigl( \mathbf{1}[(\mathrm{true}, y, z) \in s]\, p(\mathrm{true}, y, z) + \mathbf{1}[(\mathrm{false}, y, z) \in s]\, p(\mathrm{false}, y, z) \Bigr).$$
