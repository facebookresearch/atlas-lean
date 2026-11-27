# Threshold and Belyakov transition of the logistic SIR model without vaccination

**Setting.** Let $A, \beta, \mu, d, g > 0$ and $\sigma = \mu + d$. Consider the SIR system with logistically growing susceptibles and no vaccination, reduced to the $(S, I)$ plane:

$$\dot S = S(A - S) - \beta I S, \qquad \dot I = \beta I S - (\sigma + g) I,$$

with basic reproduction number $\mathcal{R}_0 = A\beta/(\sigma+g)$. Its equilibria are $E_0 = (0,0)$, $E_1 = (A, 0)$ and

$$E_2 = \Big(\frac{A}{\mathcal{R}_0}, \frac{A}{\beta}\Big(1 - \frac{1}{\mathcal{R}_0}\Big)\Big),$$

which lies in the open first quadrant exactly when $\mathcal{R}_0 > 1$.

**Lemma.**

1. $E_0$ is a saddle for every $\mathcal{R}_0 > 0$.
2. $E_1$ is a sink if $\mathcal{R}_0 < 1$ and a saddle if $\mathcal{R}_0 > 1$; at $\mathcal{R}_0 = 1$ it undergoes a transcritical bifurcation with $E_2$.
3. If $1 < \mathcal{R}_0 < 1 + \frac{1}{4\beta}$, then $E_2$ is a stable node; if $\mathcal{R}_0 > 1 + \frac{1}{4\beta}$, then $E_2$ is a stable focus; at $\mathcal{R}_0 = 1 + \frac{1}{4\beta}$ it undergoes a Belyakov transition (its eigenvalues pass from real to complex).

So without vaccination the transcritical bifurcation at $\mathcal{R}_0 = 1$ is the threshold for endemicity: for $\mathcal{R}_0 < 1$ the disease-free state $E_1$ is the only stable equilibrium, and for $\mathcal{R}_0 > 1$ the endemic equilibrium $E_2$ is the stable one.

## Expansion

The Jacobian at a point $(S, I)$ is $\begin{pmatrix} A - 2S - \beta I & -\beta S \\ \beta I & \beta S - (\sigma+g) \end{pmatrix}$. At $E_0$ its eigenvalues are $A > 0$ and $-(\sigma+g) < 0$. At $E_1$ they are $-A$ and $A\beta - (\sigma+g)$, whose sign is that of $\mathcal{R}_0 - 1$. At $E_2$ the trace is $-(\sigma+g)/\beta < 0$ and the determinant is positive for $\mathcal{R}_0 > 1$, so $E_2$ is stable; the discriminant changes sign at the stated value of $\mathcal{R}_0$, which separates the node and focus regimes. This is the $p = 0$ slice of the two-parameter bifurcation diagram in which vaccination is added.

## Sources

- J. P. S. Maurício de Carvalho and A. A. Rodrigues, "SIR model with vaccination: bifurcation analysis", arXiv:2211.16339 (2022): Section 5 (the case without vaccination), Lemma 2. <https://doi.org/10.48550/arXiv.2211.16339>. Published version: Qualitative Theory of Dynamical Systems 22(3) (2023), article 105, <https://doi.org/10.1007/s12346-023-00802-2>; locators above refer to the arXiv version.
