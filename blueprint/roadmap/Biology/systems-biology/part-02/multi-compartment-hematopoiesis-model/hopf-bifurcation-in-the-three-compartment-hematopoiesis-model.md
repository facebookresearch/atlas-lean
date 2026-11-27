# Hopf bifurcation in the three-compartment hematopoiesis model

**Setting.** In the three-compartment model of stem ($u_1$), progenitor ($u_2$) and mature white blood cells ($u_3$) with proliferation rates $p_1, p_2$, maximal self-renewal fractions $a_1, a_2$, mature-cell death rate $d_3$ and feedback $1/(1+k u_3)$, assume $a_1 > \tfrac12$ and $a_2 < a_1$, so that the positive steady state $E_2$ exists. Let $\beta, \gamma > 0$ and the critical progenitor proliferation rate

$$p_2^* = \frac{p_1}{1 - a_2/a_1}\Big[\frac{1}{\gamma} - \beta\frac{d_3}{p_1}\Big]$$

be as in the stability criterion for $E_2$.

**Theorem.** Let $d_3^{\max} = p_1/(\beta\gamma)$ and $d_3 < d_3^{\max}$ (so $p_2^* > 0$). Then $E_2$ undergoes a Hopf bifurcation at $p_2 = p_2^*$: the Jacobian at $E_2$ has a pair of complex conjugate eigenvalues $\lambda_{1,2}(p_2) = \mu(p_2) \pm i\,\omega(p_2)$ with

$$\mu(p_2^*) = 0, \qquad \omega(p_2^*) \ne 0, \qquad \frac{d\mu}{dp_2}(p_2^*) \ne 0,$$

while the third eigenvalue stays real and negative. The source proves only these Hopf conditions (Theorem 7, Remark 9); it does not compute the first Lyapunov coefficient, and shows supercriticality only numerically, for $a_1=0.7$, $a_2=0.5$, $p_1=1$, $d_3=0.1337$ (its Fig. 3, where $p_2^*=0.3937$ and a stable limit cycle appears for $p_2<p_2^*$).

For $p_1 = 1$ the set of parameters $(a_1, a_2, d_3, p_2) \in (0,1)^2 \times \mathbb{R}_+^2$ with $a_1 > \tfrac12$, $a_1 > a_2$ and $E_2$ unstable is bounded, so oscillations require a restricted parameter combination.

## Expansion

With characteristic polynomial $P(x) = x^3 + c_1 x^2 + c_2 x + c_3$ at $E_2$, a nonzero purely imaginary pair occurs exactly when $c_1 c_2 = c_3$, which is the condition $p_2 = p_2^*$. Transversality follows from the identity $c_1 c_2 - c_3 = -P(\lambda_1 + \lambda_2 + \lambda_3)$: differentiating in $p_2$ gives $2\mu'(p_2^*)(\lambda_3^2 + \omega^2)$ on one side and an explicit nonzero expression on the other, so $\mu'(p_2^*) < 0$. The third eigenvalue at the bifurcation equals $-c_1$, which is negative, so orbits approach a two-dimensional center manifold carrying the Hopf normal form. Where the bifurcation is supercritical, as in the numerical example, the resulting stable limit cycle gives sustained oscillations of mature white blood cell counts, as seen in cyclic neutropenia and some leukemias, without any explicit delay: the chain of compartments acts as a distributed delay. The parameters at which it appears differ from those identified for healthy hematopoiesis in at least two cell properties.

## Depends on

- [Steady states and stability of the three-compartment hematopoiesis model](steady-states-and-stability-of-the-three-compartment-hematopoiesis-model.md)

## Sources

- F. Knauer, T. Stiehl and A. Marciniak-Czochra, "Oscillations in a white blood cell production model with multiple differentiation stages", arXiv:1812.02017 (2018), Proposition 5, Theorem 7 and Remark 9, with the numerical example of Fig. 3, <https://doi.org/10.48550/arXiv.1812.02017>.
