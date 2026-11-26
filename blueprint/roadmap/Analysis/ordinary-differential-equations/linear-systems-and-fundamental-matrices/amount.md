# Solution of the constant-input relaxation equation

For $k, R, A_0 \in \mathbb{R}$, the solution of $A' = R - kA$ with constant input $R$ and initial value $A(0) = A_0$ is

$$A(t) = A_0\,e^{-kt} + \int_0^t e^{-k(t - s)}\,R\,ds \qquad (t \in \mathbb{R}),$$

with the integral oriented, so that for $t < 0$ it is $-\int_t^0$.
