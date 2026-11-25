# The Butler-Volmer current is a strictly increasing function of the overpotential

This node covers the inversion of the Butler-Volmer relation. For an exchange current density $j_0 > 0$, transfer coefficients
$\alpha_a, \alpha_c > 0$, temperature $T > 0$ and $f = F/(RT)$, the Butler-Volmer current density

$$j(\eta) = j_0\left(e^{\alpha_a f\eta} - e^{-\alpha_c f\eta}\right)$$

is a smooth strictly increasing bijection of $\mathbb{R}$ onto $\mathbb{R}$ with $j(0) = 0$ and $j'(0) = j_0(\alpha_a + \alpha_c) f$. Hence each
current density has exactly one activation overpotential, which has the sign of the current. For $\alpha_a f\eta \to \infty$ the anodic
branch satisfies $\eta - \frac{1}{\alpha_a f}\ln\frac{j}{j_0} \to 0$ (Tafel behaviour).

## Expansion

A good expansion states the Butler-Volmer law as a constitutive input with its parameters, proves monotonicity and surjectivity,
and derives the linear and Tafel limits. Coupling the overpotential to mass transport, ohmic losses and degradation are separate nodes.

## Sources

- A. J. Bard and L. R. Faulkner, *Electrochemical Methods: Fundamentals and Applications*, 2nd edition, Wiley, 2001, for the Butler-Volmer equation.
