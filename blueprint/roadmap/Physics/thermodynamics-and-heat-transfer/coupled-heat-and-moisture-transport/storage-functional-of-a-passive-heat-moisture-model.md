# Storage functional of a passive heat-moisture model

Let a scaled state $x(t) \in \mathbb{R}^n$ of temperature and moisture variables satisfy $C x' = -L x + f(t)$ with constant symmetric
positive definite storage matrix $C$, constant symmetric positive semidefinite coupling matrix $L$ and a continuous input $f$, the
symmetry and passivity being constitutive assumptions about the chosen scaling. Then the storage functional $V = \frac12 x^{\mathsf T} C x$
satisfies $V' = x^{\mathsf T} f - x^{\mathsf T} L x \le x^{\mathsf T} f$, and $V$ does not increase when $f = 0$. $V$ is a storage or
Lyapunov functional; identifying it with a thermodynamic energy or entropy needs a separate argument. Nonlinear sorption, condensation and
latent phase changes are excluded, and native-variable hygrothermal equations need not have this symmetric form.

## Depends on

## Proof depends on

## Expansion

Open a source for a linear coupled heat and moisture model in a scaling where the storage and coupling matrices are symmetric, and state
the correspondence of its variables with $x$.

## Sources

- H. M. Künzel, *Simultaneous Heat and Moisture Transport in Building Components*, Fraunhofer IRB, 1995.
