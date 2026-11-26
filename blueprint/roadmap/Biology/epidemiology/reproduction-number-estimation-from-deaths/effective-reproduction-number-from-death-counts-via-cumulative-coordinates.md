# Effective reproduction number from death counts via cumulative-coordinate SIRD filtering

**Model.** In the SIRDC model with susceptible, infectious and resolving fractions $x_1,x_2,x_3$ (infection rate $\beta(t)$, recovery from infectiousness $\gamma$, resolution rate $\theta$, fatality fraction $\delta$), the deaths are $y=x_4=\delta[1-(x_1+x_2+x_3)]$ and

$$\dot x_1=-\beta x_1x_2,\qquad \dot x_2=\beta x_1x_2-\gamma x_2,\qquad \dot x_3=\gamma x_2-\theta x_3 .$$

The effective reproduction number is $R=\beta x_1/\gamma$. In the cumulative coordinates $z_1=x_1$, $z_2=x_1+x_2$, $z_3=x_1+x_2+x_3$ the nonlinearity is confined to the first equation:

$$\dot z_1=-\gamma R\,(z_2-z_1),\qquad \dot z_2=-\gamma(z_2-z_1),\qquad \dot z_3=-\theta(z_3-z_2),\qquad y=\delta(1-z_3),$$

with structural constraints $z_i\in[0,1]$, $z_1\le z_2\le z_3$ and $z_1$ nonincreasing. Its Euler discretization gives the direct estimate

$$\hat R(k)=\frac{z_1(k)-z_1(k+1)}{\gamma\bigl(z_2(k)-z_1(k)\bigr)} .$$

**Proposition (unconstrained estimator is a linear filter).** Reconstructing $z_1,z_2$ recursively from noise-free deaths is equivalent to driving the time-invariant linear filter $\hat x(k+1)=A\hat x(k)+B\hat u(k)$, $\hat z(k)=C\hat x(k)+D\hat u(k)$ with

$$A=\begin{bmatrix}0&0\\1&0\end{bmatrix},\quad B=\begin{bmatrix}1\\0\end{bmatrix},\quad C=\begin{bmatrix}\theta^{-1}+\gamma^{-1}-2\theta^{-1}\gamma^{-1}&(1-\theta^{-1})(1-\gamma^{-1})\\ \theta^{-1}&1-\theta^{-1}\end{bmatrix},\quad D=\begin{bmatrix}\gamma^{-1}\theta^{-1}\\0\end{bmatrix}$$

by the input $\hat u(k)=1-\delta^{-1}y(k)$ and substituting $\hat z_1,\hat z_2$ into $\hat R(k)$. For $k\ge2$ the resulting $\hat R(k)$ is *independent of the fatality rate* $\delta$.

**Constrained estimation.** Because noisy data make the filtered $\hat z$ violate the structural constraints (and $\hat R$ swing negative or very large), estimate instead by the convex program that minimizes the weighted residual $\frac1N\sum_kq(k)(y(k)-\delta\hat y(k))^2$ over filter trajectories with nonnegative input $\hat u\ge0$ and linear constraints encoding $z_i\in[0,1]$, $z_1\le z_2\le z_3$ and monotone $z_1$, then set $\hat R(k)=\hat u(k)/(\gamma(\hat z_2(k)-\hat z_1(k)))$. This estimate is again independent of $\delta$, and the constraints keep all reconstructed compartments in their physical ranges without pre-smoothing the data.

## Expansion

Summing compartments turns the SIR flows into a cascade in which each cumulative variable relaxes toward the next one, and only $z_1$ carries the unknown $R$. Inverting the measurement $z_3=1-y/\delta$ and the two linear relaxation equations expresses $z_2,z_1$ as finite linear combinations of past measurements, which is the stated state-space filter. Rescaling $y$ by $\delta$ rescales the deviations $1-z_i$ by a common factor in the linear part, and $\hat R$ is a ratio of two such deviations, so $\delta$ cancels; the same scaling argument applies to the minimizer of the constrained problem. Measurement weights $q(k)=v(k)^{-1}$ correspond to Gaussian white measurement noise.

## Sources

- M. C. de Oliveira, "Estimating the Effective Reproduction Number and Variables of Disease Models for the COVID-19 Epidemic", arXiv:2008.08201 (2020), Section 2 (SIRDC model, change of coordinates, discrete-time model), Section 3 (unconstrained estimation, linear-filter realization and Proposition 1) and Section 4 (constrained estimation problems and Proposition 2). <https://doi.org/10.48550/arXiv.2008.08201>
