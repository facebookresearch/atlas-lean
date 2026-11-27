# Product-form stationary measures under non-mass-action kinetics force complex balance

**Setting.** A reaction network $\{\mathcal S, \mathcal C, \mathcal R\}$ has $m$ species and reactions $y_k \to y_k'$ with rate constants $\kappa_k > 0$. Its stochastic model is a continuous-time Markov chain on $\mathbb Z^m_{\ge 0}$ with general (Kelly–Whittle) intensities

$$\lambda_k(x) = \kappa_k \prod_{i=1}^m \theta_i(x_i)\,\theta_i(x_i - 1)\cdots\theta_i(x_i - y_{ki} + 1),$$

where $\theta_i : \mathbb Z \to \mathbb R_{\ge 0}$ is the "rate of association" of species $i$ and $\theta_i(x) = 0$ for $x \le 0$. Mass action is $\theta_i(x) = x$. The associated deterministic model is mass-action $\dot x = \sum_k \kappa_k x^{y_k}(y_k' - y_k)$. If it has a complex-balanced equilibrium $c$, the stochastic model has the product-form stationary measure

$$\pi(x) = \prod_{i=1}^m \frac{c_i^{x_i}}{\theta_i(1)\cdots\theta_i(x_i)}, \qquad x \in \mathbb Z^m_{\ge 0}.$$

**Theorem (normalizability and non-explosivity).** Suppose the associated mass-action system is complex balanced with equilibrium $c \in \mathbb R^m_{>0}$ and $\lim_{x\to\infty}\theta_i(x) = \infty$ for every $i$. Then $\pi$ is summable over $\mathbb Z^m_{\ge 0}$, so a stationary distribution exists, and the stochastic model is non-explosive.

**Theorem (converse).** Suppose $\lim_{x\to\infty}\theta_i(x) = \infty$ for every $i$, and that for some $c \in \mathbb R^m_{\ge 0}$ the measure $\pi$ above is stationary for the stochastic model. Then $c$ is a complex-balanced equilibrium of the associated deterministic mass-action model with the same rate constants. The same conclusion holds when each $\lim_{x\to\infty}\theta_i(x) \in \{0, \infty\}$ and $\theta_i(x) > 0$ for all large $x$.

## Depends on

- [Non-explosivity of complex-balanced stochastic reaction networks](../non-explosivity-of-complex-balanced-stochastic-reaction-networks.md)
- [Complex-balanced concentrations](../../complex-balancing-and-the-deficiency-zero-theore/is-complex-balanced.md)
- [Mass-action vector field](../../../../Dynamics/smooth-dynamics/mass-action-field.md)

## Expansion

Summability factorizes over species, and the ratio test gives $c_i/\theta_i(x+1) \to 0$. Non-explosivity follows from the criterion $\sum_x \pi(x)\sum_k\lambda_k(x) < \infty$, where the intensities cancel all but finitely many factors of the product-form denominator. For the converse, substituting $\pi$ into the stationarity equation and cancelling gives

$$\sum_{z\in\mathcal C}\Theta_z(x)\sum_{k:\,y_k'=z}c^{y_k - y_k'}\kappa_k = \sum_{z\in\mathcal C}\Theta_z(x)\sum_{k:\,y_k=z}\kappa_k, \qquad \Theta_z(x) = \prod_{i}\theta_i(x_i)\cdots\theta_i(x_i - z_i + 1).$$

When $\theta_i \to \infty$, the functions $\{\Theta_z\}_{z\in\mathcal C}$ are linearly independent; this is proved by induction on the number of species, comparing growth orders. So the coefficients match complex by complex, which is exactly complex balance. When some $\theta_i \to 0$, pass to $1/\theta_i$ and clear denominators. This extends the mass-action converse of Cappelletti and Wiuf.

## Sources

- David F. Anderson and Tung D. Nguyen, "Results on stochastic reaction networks with non-mass action kinetics", Mathematical Biosciences and Engineering 16 (2019), 2118–2140, <https://doi.org/10.3934/mbe.2019103>; numbering as in arXiv:1712.01716: Theorem 3.2, Theorem 4.1, Theorem 4.2 with Lemma 4.1, Corollary 1.
