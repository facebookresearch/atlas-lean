# Factored certificate gives a lower bound for the semidefinite program

Let $C$, $A_1, \dots, A_m$ and $E_1, \dots, E_p$ be Hermitian $n \times n$ complex matrices, $c_0 \in \mathbb{R}$, $b \in \mathbb{R}^m$, $d \in \mathbb{R}^p$. Suppose $\lambda \in \mathbb{R}^m$ with $\lambda_i \ge 0$, $\nu \in \mathbb{R}^p$ and an $n \times k$ complex matrix $F$ satisfy

$$C + \sum_i \lambda_i A_i + \sum_j \nu_j E_j = F F^*.$$

Then $c_0 - \sum_i \lambda_i b_i - \sum_j \nu_j d_j$ is a lower bound for $\operatorname{Re}\operatorname{tr}(C W) + c_0$ over all positive semidefinite $W$ with $\operatorname{Re}\operatorname{tr}(A_i W) \le b_i$ for all $i$ and $\operatorname{Re}\operatorname{tr}(E_j W) = d_j$ for all $j$.
