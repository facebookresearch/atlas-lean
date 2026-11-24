# The forward variables are path weights

Let $c$ be a chain CRF with a finite set of
states $S$ and weights in a semiring $R$ carrying a relation $\le$, and let $x$ be an
observation sequence. For every $t \in \mathbb{N}$ and every state $s \in S$, the forward
variable $\alpha_t(s)$ equals the total path weight of the label paths
$z = (z_0, \dots, z_t) \in S^{t+1}$ that end in $z_t = s$:

$$\alpha_t(s) = \sum_{z \in S^{t+1},\ z_t = s} w_t(z),$$

where $w_t(z)$ is the path weight of $z$.
