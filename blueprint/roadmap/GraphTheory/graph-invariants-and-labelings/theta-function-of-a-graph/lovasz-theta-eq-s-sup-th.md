# Theta is the maximum of the coordinate sum over the theta body

For every finite graph $G$,

$$
\vartheta(G) = \sup\Bigl\{\sum_v x_v : x \in \mathrm{TH}(G)\Bigr\}.
$$

Knuth takes the right-hand side as the definition of $\vartheta(G)$ and proves, following Grötschel, Lovász and Schrijver, that it equals the min-max form $\vartheta_1$, together with three other characterisations (his eq. (5.1)); the inequality $\sup_{\mathrm{TH}(G)} \sum_v x_v \le \vartheta_1(G)$ is the easy direction (his Lemma 5), and the reverse rests on a duality principle for semidefinite matrices (his §§7-12).

## Sources

- D. E. Knuth, *The Sandwich Theorem*, Electron. J. Combin. 1 (1994), #A1, arXiv:math/9312214v1, eq. (5.1) with unit weights, and §§5-12.
