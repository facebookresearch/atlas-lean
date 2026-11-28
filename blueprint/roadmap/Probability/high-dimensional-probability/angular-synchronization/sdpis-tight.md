# Tightness of the angular synchronization SDP

For a matrix $C \in \mathbb{C}^{n \times n}$, the semidefinite relaxation

$$\max \operatorname{Re} \operatorname{tr}(C X) \quad \text{over Hermitian } X \succeq 0 \text{ with } X_{kk} = 1 \text{ for all } k$$

is tight with a unique solution if there is $\hat{x} \in \mathbb{C}^n$ that is a global maximizer of $\operatorname{Re}(x^* C x)$ over vectors with $\lvert x_k \rvert = 1$ for all $k$, unique up to a global phase, such that for every feasible $X$,

$$\operatorname{Re} \operatorname{tr}(C X) \le \operatorname{Re} \operatorname{tr}(C \hat{x} \hat{x}^*),$$

with equality only for $X = \hat{x} \hat{x}^*$.
