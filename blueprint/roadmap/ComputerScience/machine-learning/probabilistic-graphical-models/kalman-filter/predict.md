# Kalman prediction

Given real $n \times n$ matrices $F$ and $Q$, the prediction of a
belief with mean $m$ and covariance $P$ is the belief with mean $F m$ and covariance
$F P F^\top + Q$. It models the dynamics $x' = F x + w$ with process noise $w \sim N(0, Q)$.
