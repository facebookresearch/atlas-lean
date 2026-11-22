# Probability of an event as the expectation of its indicator

Let $E$ be a finite set, $p$ a real number and $A \subseteq \{0, 1\}^E$. Then

$$P_p(A) = \sum_{\omega \in A} \prod_{e \in E} w_p(\omega_e) = \mathbb{E}_p[1_A],$$

where $w_p(1) = p$, $w_p(0) = 1 - p$ and $\mathbb{E}_p$ is the [expectation](../../osss-inequality-for-decision-trees/expect.md) under these product weights.
