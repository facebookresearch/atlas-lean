# Extremal values and moments of the quadratic Colless index

**Definition.** For a rooted bifurcating phylogenetic tree $T$ with $n$ leaves, the balance value of an internal node $v$ with children $v_1, v_2$ is $\mathrm{bal}_T(v) = |\kappa_T(v_1) - \kappa_T(v_2)|$, where $\kappa_T(w)$ is the number of leaves below $w$. The Colless index is $C(T) = \sum_v \mathrm{bal}_T(v)$; the *quadratic Colless index* (Q-Colless index) is

$$QC(T) = \sum_{v \in V_{\rm int}(T)} \mathrm{bal}_T(v)^2 = \sum_{v \in V_{\rm int}(T)} \big(\kappa_T(v_1) - \kappa_T(v_2)\big)^2 .$$

For example $QC(K_7) = 55$ for the 7-leaf caterpillar (comb) and $QC(B_7) = 2$ for the maximally balanced 7-leaf tree.

**Theorem (minimum).** On bifurcating trees with $n$ leaves, $QC$ is minimized exactly at the maximally balanced tree $B_n$ (each internal node splits its leaves as $\lceil k/2\rceil, \lfloor k/2\rfloor$), and only there. All its balance values are $0$ or $1$, so $QC(B_n) = C(B_n)$.

**Theorem (maximum).** $QC$ is maximized exactly at the caterpillar $K_n$, and only there, with

$$QC(K_n) = \binom n3 + \binom{n-1}3 .$$

Unlike the ordinary Colless index, whose minimum is attained by many trees, $QC$ therefore has unique minimizing and maximizing trees, a desirable property for a balance index.

**Theorem (uniform model).** Under the uniform distribution on bifurcating trees with $n$ labeled leaves,

$$\mathbb E_U(QC_n) = \binom{n+1}{2}\frac{(2n-2)!!}{(2n-3)!!} - n(2n-1),$$

and the variance has an explicit closed form in $n$ and $\frac{(2n-2)!!}{(2n-3)!!}$.

**Theorem (Yule model).** With $H_n = \sum_{i\le n} 1/i$ and $H^{(2)}_n = \sum_{i\le n}1/i^2$,

$$\mathbb E_Y(QC_n) = n(n+1) - 2nH_n, \qquad \sigma^2_Y(QC_n) = \frac13\,n\big(n^3 - 8n^2 + 50n - 1 - 30H_n - 12nH^{(2)}_n\big).$$

## Expansion

$QC$ satisfies the recursion $QC(T_1 * T_2) = QC(T_1) + QC(T_2) + (n_1 - n_2)^2$ for the tree with root subtrees $T_1, T_2$ of sizes $n_1, n_2$. Since squares penalize unequal splits convexly, exchanging subtrees to equalize splits strictly lowers $QC$ (minimum at $B_n$), and pushing all leaves to one side strictly raises it, the caterpillar contributing $\sum_{k=2}^{n}(k-2)^2 = \binom n3 + \binom{n-1}3$. The moments follow from the recursion together with the split distributions of the uniform and Yule models via generating functions.

## Sources

- Tomás M. Coronado, Arnau Mir and Francesc Rosselló, "Squaring within the Colless index yields a better balance index", arXiv:2007.14731 (2020), Section 3: Theorem 3 (minimum), Theorem 4 (maximum), Theorem 5 (uniform model moments), Theorem 6 (Yule model moments), <https://doi.org/10.48550/arXiv.2007.14731>.
