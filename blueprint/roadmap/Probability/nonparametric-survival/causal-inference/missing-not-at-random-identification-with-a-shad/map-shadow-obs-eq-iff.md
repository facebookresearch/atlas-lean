# The observed-data law

Let $\mathcal{Y}$ and $\mathcal{Z}$ be finite sets with measurable singletons, and let $P$ and $Q$ be finite measures on $\{\mathrm{true}, \mathrm{false}\} \times \mathcal{Y} \times \mathcal{Z}$ (coordinates $R$, $Y$, $Z$). The observed-data map sends $(r, y, z)$ to $(z, y)$ if $r = \mathrm{true}$ and to $(z, \ast)$ if $r = \mathrm{false}$, with values in $\mathcal{Z} \times (\mathcal{Y} \sqcup \{\ast\})$. Then $P$ and $Q$ have the same image measure under the observed-data map if and only if

- $P(\{(\mathrm{true}, y, z)\}) = Q(\{(\mathrm{true}, y, z)\})$ for all $y \in \mathcal{Y}$ and $z \in \mathcal{Z}$, and
- $\sum_{y} P(\{(\mathrm{false}, y, z)\}) = \sum_{y} Q(\{(\mathrm{false}, y, z)\})$ for every $z \in \mathcal{Z}$, that is, $P(R = \mathrm{false}, Z = z) = Q(R = \mathrm{false}, Z = z)$.
