# On-average replace-one stability

Fix a sample size $m \ge 1$, a real-valued loss $L(h, z)$ of a hypothesis $h$ at an example $z \in \mathcal Z$, a learner
$A$ mapping a sample $S \in \mathcal Z^m$ and a seed $r$ to a hypothesis $A(S, r)$, a probability law $\rho$ on the
seeds, and $\varepsilon \in \mathbb R$. For a probability law $\nu$ on $\mathcal Z$, draw a sample
$S = (z_1, \dots, z_m)$ of $m$ independent examples from $\nu$, a fresh example $z' \sim \nu$, an index $i$ uniform on
$\{1, \dots, m\}$ and a seed $r \sim \rho$, all independently, and let $S^{(i)}$ be $S$ with $z_i$ replaced by $z'$.
The learner is on-average replace-one stable at $\varepsilon$ if, for every $\nu$ under which both
$L(A(S^{(i)}, r), z_i)$ and $L(A(S, r), z_i)$ are integrable,

$$\mathbb{E}\bigl[L(A(S^{(i)}, r), z_i) - L(A(S, r), z_i)\bigr] \le \varepsilon .$$

Both runs use the same seed, and both losses are taken at the original example $z_i$. The source states the
definition without seeds, with a decreasing rate $\varepsilon(m)$ over all sample sizes; this is the bound at one sample
size, for a learner with a random seed.

## Sources

- S. Shalev-Shwartz and S. Ben-David, *Understanding Machine Learning: From Theory to Algorithms*, Cambridge University Press, 2014 (author copy), Definition 13.3 (on-average-replace-one-stable). <https://www.cs.huji.ac.il/~shais/UnderstandingMachineLearning/understanding-machine-learning-theory-algorithms.pdf>
