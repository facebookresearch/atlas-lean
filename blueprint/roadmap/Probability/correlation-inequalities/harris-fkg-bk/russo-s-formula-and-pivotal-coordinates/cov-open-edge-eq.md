# Covariance with one coordinate, for an arbitrary event

Let $E$ be a finite set, $p \in \mathbb{R}$, $A \subseteq \{0,1\}^E$ an arbitrary event (not necessarily increasing) and $e \in E$. Write $O_e = \{\omega : \omega(e) = 1\}$. Then

$$P_p(A \cap O_e) - P_p(O_e)\,P_p(A) = p(1-p)\Big(\sum_{\omega \in A,\ \omega(e) = 1} W_p^{(e)}(\omega) - \sum_{\omega \in A,\ \omega(e) = 0} W_p^{(e)}(\omega)\Big),$$

where $P_p$ is the [Bernoulli weight](prob.md) and $W_p^{(e)}$ the [product of the coordinate weights off $e$](weight-off.md). For $p \in [0,1]$ the left-hand side is the covariance of $\mathbf{1}_A$ with the state of $e$.
