# A calibration matrix is identifiable iff its kernel is trivial

For every real $m \times n$ matrix $A$, the calibration model $y = A\theta$ is
[identifiable](identifiable.md), that is, $\theta \mapsto A\theta$ is injective, if and only if

$$A\theta = 0 \implies \theta = 0 \qquad \text{for every } \theta \in \mathbb{R}^n .$$

The forward direction compares $\theta$ with $0$; the converse applies the hypothesis to
$\theta_1 - \theta_2$, whose image $A\theta_1 - A\theta_2$ vanishes when the observations agree.
