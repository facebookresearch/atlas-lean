# Inverse congruence with the global-to-material strain map

For $\theta \in \mathbb{R}$ let $T_e(\theta)$ be the global-to-material engineering-strain transformation

$$T_e(\theta) = \begin{pmatrix} c^2 & s^2 & cs \\ s^2 & c^2 & -cs \\ -2cs & 2cs & c^2 - s^2 \end{pmatrix}, \qquad c = \cos\theta,\ s = \sin\theta,$$

and for a real $3 \times 3$ matrix $Q$ let $\bar Q(\theta) = T_e(\theta)^\top Q\,T_e(\theta)$ be the global stiffness of the lamina at angle $\theta$. Then

$$\big(T_e(\theta)^{-1}\big)^{\top} Q\,T_e(\theta)^{-1} = \bar Q(-\theta).$$
