# Logarithmic-derivative forced Burgers field

For a real initial velocity $u_0$ and anchor $a$, put

$$
g(x)=\exp\left(-\frac{1}{2\nu}\int_a^x u_0(y)\,dy\right),\qquad
\Phi(t,x)=\operatorname{potentialHeatSolution}(\nu,q,g)(t,x),\qquad
u_q(t,x)=-2\nu\frac{\partial_x\Phi(t,x)}{\Phi(t,x)}.
$$

The field $u_q$ is the Cole–Hopf logarithmic derivative of this specified profile. This is a definition for arbitrary real parameters and data; evolution statements apply under positive viscosity and the regularity hypotheses of the corresponding theorem. In Lean, ordinary derivatives and real division are total operations, so the definition alone makes no positivity or differentiability assertion.

The transform identity is described in Gesztesy and Holden, [The Cole–Hopf and Miura transformations revisited](https://arxiv.org/abs/solv-int/9812025), Lemmas 3.1–3.2 and Theorem 3.3(ii).
