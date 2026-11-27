# Uniqueness of the transformed lamina stiffness

For $\theta \in \mathbb{R}$ let $T_e(\theta)$ and $T_s(\theta)$ be the global-to-material engineering-strain and stress transformations

$$T_e(\theta) = \begin{pmatrix} c^2 & s^2 & cs \\ s^2 & c^2 & -cs \\ -2cs & 2cs & c^2 - s^2 \end{pmatrix}, \qquad c = \cos\theta,\ s = \sin\theta,$$

$$T_s(\theta) = \begin{pmatrix} c^2 & s^2 & 2cs \\ s^2 & c^2 & -2cs \\ -cs & cs & c^2 - s^2 \end{pmatrix}.$$

For real $3 \times 3$ matrices $Q$ and $Q_g$,

$$\big(\forall e \in \mathbb{R}^3,\ T_s(\theta)\,(Q_g\,e) = Q\,(T_e(\theta)\,e)\big) \iff Q_g = T_e(\theta)^\top Q\,T_e(\theta).$$
