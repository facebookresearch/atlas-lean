# Probability flux of a diffusion

For $D \in \mathbb{R}$, a drift $b : \mathbb{R}^n \to \mathbb{R}^n$ and a density $p : \mathbb{R}^n \to \mathbb{R}$, the probability
flux is the vector field

$$J(x) = b(x)\, p(x) - D \nabla p(x),$$

with $\nabla p$ the [gradient](grad.md). The definition allows every real $D$. For $D \ge 0$ and a
sufficiently regular density $p$ of the diffusion $dX = b\, dt + \sqrt{2D}\, dW$, it is the
probability flux of that diffusion.
