# Minimal minimum isolating cuts lie in disjoint bit-cut regions

Let $G = (V, E, w)$, $R \subseteq V$ with $|R| \ge 2$, and $L = \lceil \log_2 |R| \rceil$. Assign distinct labels $b(v) \in \{0,1\}^L$ to the terminals $v \in R$. For $i = 1, \dots, L$ let $R_i^0 = \{v \in R : b(v)_i = 0\}$ and $R_i^1 = R \setminus R_i^0$, and let $X_i$ be a minimum $(R_i^0, R_i^1)$-cut, i.e. $R_i^0 \subseteq X_i \subseteq V \setminus R_i^1$ minimizing $w(\partial X_i)$ (if one of the two sets is empty put $X_i = V$ or $X_i = \emptyset$ accordingly). For $v \in R$ define the region

$$
U_v = \bigcap_{i \,:\, b(v)_i = 0} X_i \;\cap \bigcap_{i \,:\, b(v)_i = 1} (V \setminus X_i).
$$

Then (a) $v \in U_v$ and $U_v \cap R = \{v\}$; (b) $U_u \cap U_v = \emptyset$ for distinct $u, v \in R$; and (c) the minimal minimum $v$-isolating cut satisfies $S_v^{*} \subseteq U_v$.

## Proof sketch

Parts (a) and (b) hold because distinct labels differ in some coordinate $i$, which places the two regions on opposite sides of $X_i$. For (c) fix $i$ with $b(v)_i = 0$ and put $S = S_v^{*}$. The set $S \cup X_i$ still contains $R_i^0$ and avoids $R_i^1$ (because $S \cap R = \{v\} \subseteq R_i^0$), so $w(\partial(S \cup X_i)) \ge w(\partial X_i)$, and submodularity of the cut function gives $w(\partial(S \cap X_i)) \le w(\partial S)$. Since $S \cap X_i$ is again $v$-isolating, it is a minimum $v$-isolating cut, and minimality of $S_v^{*}$ forces $S \subseteq X_i$; the case $b(v)_i = 1$ is symmetric with $V \setminus X_i$.

## Depends on

- [Maximum-flow oracles and the max-flow call model for cut problems](max-flow-oracle-call-model.md)
- [Minimum isolating cuts of a terminal set](minimum-isolating-cuts.md)

## Proof depends on

- [Minimum isolating cuts are closed under intersection and union](isolating-cuts-lattice.md)
- [Submodular set function](../../../../approximation-algorithms/maximum-n-times-coverage/is-submodular.md)

## Sources

- Jason Li, Debmalya Panigrahi, "Deterministic Min-cut in Poly-logarithmic Max-flows", FOCS (2020), arXiv:2111.02008.
- Chandra Chekuri, Kent Quanrud, "Isolating Cuts, (Bi-)Submodularity, and Faster Algorithms for Connectivity", ICALP (2021), arXiv:2103.12908.
