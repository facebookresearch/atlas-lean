# Almost every point is a Lebesgue point, for doubling measures

Let $X$ be a pseudometric space with a second countable topology and its Borel σ-algebra, and let
$\mu$ be a locally finite measure on $X$ that is uniformly locally doubling: there are $C \ge 0$ and $r_0 > 0$ such that
$\mu(\bar B(x, 2r)) \le C \, \mu(\bar B(x, r))$ for every $x \in X$ and every $r$ with $0 < r < r_0$, where $\bar B$
denotes a closed ball. Let $E$ be a normed additive commutative group, let
$f \colon X \to E$ be locally integrable for $\mu$, and let $K \in \mathbb{R}$. Then for $\mu$-almost every
$x \in X$ the following holds: whenever points $w_j \in X$ and radii $\delta_j$, indexed along a filter (for instance
a sequence), satisfy $\delta_j \to 0$ with eventually $\delta_j > 0$ and $x \in \bar B(w_j, K\delta_j)$, the averages

$$\frac{1}{\mu(\bar B(w_j, \delta_j))} \int_{\bar B(w_j, \delta_j)} \|f(y) - f(x)\| \, d\mu(y)$$

tend to $0$.
