# Two-state generators are equal-input generators

Let $\lambda_0, \lambda_1 \in \mathbb{R}$ with $\Lambda = \lambda_0 + \lambda_1 \ne 0$. Then

$$\begin{pmatrix} -\lambda_0 & \lambda_0 \\ \lambda_1 & -\lambda_1 \end{pmatrix} = \Lambda\, (\mathbf 1 \pi^\top - I), \qquad \pi = \Bigl(\frac{\lambda_1}{\Lambda}, \frac{\lambda_0}{\Lambda}\Bigr):$$

the generator of the two-state chain that leaves state $0$ at rate $\lambda_0$ and state $1$ at
rate $\lambda_1$ is the [equal-input generator](equal-input-rate.md) with total rate $\Lambda$. The
matrix is a rate matrix when $\lambda_0, \lambda_1 \ge 0$. With nonnegative rates and
$\Lambda = 0$ both rates vanish and the generator is $0$; that case is excluded.
