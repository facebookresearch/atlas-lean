# Measure Mutual Information gaussian Input rank One

Let $\iota$ and $\kappa$ be finite index sets with $\iota$ nonempty, $H \in \mathbb{R}^{\iota \times \kappa}$, $v \in \mathbb{R}^\kappa$ and $R \in \mathbb{R}^{\iota \times \iota}$ positive definite. For the input $X \sim \mathcal{N}(0, v v^{\mathsf{T}})$ (a singular covariance as soon as $\lvert\kappa\rvert \ge 2$) and output $HX + Z$ with $Z \sim \mathcal{N}(0, R)$ independent of $X$, the mutual information of the joint law is

$$I(X; HX + Z) = \frac{\ln\left(1 + (Hv)^{\mathsf{T}} R^{-1} (Hv)\right)}{2 \ln 2} \text{ bits}.$$
