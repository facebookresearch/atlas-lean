# One step of recursive least squares

From the estimate $\theta$, the matrix $P$, the regressor $\varphi$ and the new observation $y$, one step of recursive
least squares returns

$$\theta' = \theta + \frac{P \varphi \,(y - \varphi^\top \theta)}{1 + \varphi^\top P \varphi}, \qquad
P' = P - \frac{P \varphi \varphi^\top P}{1 + \varphi^\top P \varphi}.$$

Division by zero gives $0$, so when $1 + \varphi^\top P \varphi = 0$ the step returns $(\theta, P)$ unchanged; for
positive semidefinite $P$, as in the algorithm, the denominator is at least $1$.

This is Algorithm 1, equations (2)–(4), of Xie, Zhang and Guo, *Convergence of a distributed least squares*, IEEE Trans. Automat. Control, accepted version (2020), DOI 10.1109/TAC.2020.3047989, with a single sensor (their Remark 2.1: with the identity adjacency
matrix the distributed algorithm is the classical one at each sensor).

## Background

- [Kalman filter update](../../../ComputerScience/machine-learning/probabilistic-graphical-models/kalman-filter/update.md): with the constant state $\theta' = \theta$, observation matrix $\varphi^\top$
  and unit observation noise variance, the Kalman gain is $P \varphi / (1 + \varphi^\top P \varphi)$ and the Kalman
  update is exactly this step.
