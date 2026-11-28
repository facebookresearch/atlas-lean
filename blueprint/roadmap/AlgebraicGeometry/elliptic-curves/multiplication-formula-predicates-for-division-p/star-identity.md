# Star identity

Let $W$ be a Weierstrass curve over a commutative ring $R$, and for
$i \in \mathbb{Z}$ let $\Phi_i$ and $\Psi_i^2$ be the polynomials `W.Φ i` and `W.ΨSq i` in $R[X]$.
The star identity at $j \in \mathbb{Z}$ is the equation in $R[X]$

$$2X\Phi_j\left(\Phi_j + X\Psi_j^2\right) + b_2X\Phi_j\Psi_j^2
+ b_4\left(\Phi_j + X\Psi_j^2\right)\Psi_j^2 + b_6\left(\Psi_j^2\right)^2
= \Phi_{j+1}\Psi_{j-1}^2 + \Phi_{j-1}\Psi_{j+1}^2,$$

where $b_2, b_4, b_6$ are the coefficients of $W$, read as constant polynomials. It drives the
induction step of the multiplication formula. As an equality of polynomials it is stronger than the
source's statement that the two sides have the same value at every $t \in R$: over a finite ring,
two different polynomials can take the same value at every point. `StarIdentity.eval` gives the
pointwise form.
