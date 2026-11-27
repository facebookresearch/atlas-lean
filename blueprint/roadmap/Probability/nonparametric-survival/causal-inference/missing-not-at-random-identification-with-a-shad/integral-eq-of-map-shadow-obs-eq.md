# Every outcome integral is identified

Let $\mathcal{Y}$ and $\mathcal{Z}$ be finite sets with measurable singletons, and let $P$ and $Q$ be finite measures on $\{\mathrm{true}, \mathrm{false}\} \times \mathcal{Y} \times \mathcal{Z}$ (coordinates $R$, $Y$, $Z$). The observed-data map sends $(r, y, z)$ to $(z, y)$ if $r = \mathrm{true}$ and to $(z, \ast)$ if $r = \mathrm{false}$, with values in $\mathcal{Z} \times (\mathcal{Y} \sqcup \{\ast\})$. Suppose both $P$ and $Q$ satisfy the shadow assumption: for every measurable $B \subseteq \mathcal{Z}$ and every $y$, $\mu(R = \mathrm{true}, Z \in B, Y = y)\, \mu(Y = y) = \mu(R = \mathrm{true}, Y = y)\, \mu(Z \in B, Y = y)$ for $\mu \in \{P, Q\}$; suppose $P$ is complete (every $g : \mathcal{Y} \to \mathbb{R}$ with $\sum_{y} P(\{(\mathrm{true}, y, z)\})\, g(y) = 0$ for all $z$ is identically $0$); and suppose $P$ and $Q$ have the same image measure under the observed-data map. Then for every $f : \mathcal{Y} \to \mathbb{R}$,

$$\int f(Y)\, dP = \int f(Y)\, dQ.$$

When $P$ and $Q$ are probability measures these integrals are the means of $f(Y)$; for other finite measures they are not (for $P = Q = 2\delta$ at a respondent and $f = 1$ both integrals are $2$).
