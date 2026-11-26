# Transcritical and node–spiral transitions in an SIRS model with vaccination

**Model.** In a population of constant size $N = S + I + R$ with birth and death rate $\mu$, transmission $\beta$, recovery $\gamma$, loss of immunity $\xi$ and vaccination flow $V$,
$$\dot S = \mu N - \frac{\beta SI}{N} - V - \mu S + \xi R,\qquad \dot I = \frac{\beta SI}{N} - (\mu + \gamma)I,\qquad \dot R = \gamma I + V - (\mu + \xi)R .$$
Two schemes are compared: constant-rate vaccination $V = \nu N$ and proportional vaccination $V = \nu S$.

**Theorem (constant scheme $V = \nu N$, $\nu < \mu + \xi$).** The infection-free equilibrium is $\mathcal O^* = \big(\tfrac{(\mu+\xi-\nu)N}{\mu+\xi}, 0, \tfrac{\nu N}{\mu+\xi}\big)$, and the endemic equilibrium has $S_E^* = (\mu+\gamma)N/\beta$ and $I_E^* = N\frac{\beta(\mu+\xi-\nu) - (\mu+\gamma)(\mu+\xi)}{\beta(\mu+\gamma+\xi)}$. Let
$$\beta^* = \frac{(\mu+\gamma)(\mu+\xi)}{\mu+\xi-\nu}.$$
For $\beta < \beta^*$, $\mathcal O^*$ is attracting and the endemic point is a saddle with $I_E^* < 0$; for $\beta > \beta^*$, $\mathcal O^*$ is a saddle and the endemic equilibrium is positive and attracting; the exchange is a transcritical bifurcation at $\beta = \beta^*$. Moreover, with $A = \mu + \gamma + \xi$, $K = 2(\gamma+\mu)^2 + \xi(4\gamma + 3\mu + \xi)$ and
$$\beta_\pm = \frac{K \pm 2\sqrt{\gamma A^3}}{\mu + \xi - \nu},$$
one has $\beta^* < \beta_-$; the endemic equilibrium is an attracting node for $\beta^* < \beta < \beta_-$ and $\beta > \beta_+$, and an attracting spiral (damped epidemic waves) for $\beta_- < \beta < \beta_+$. If $\nu > \mu + \xi$ no biologically admissible equilibrium with infection exists and the infection dies out.

**Theorem (proportional scheme $V = \nu S$).** The same structure holds with $\hat{\mathcal O}^* = \big(\tfrac{(\mu+\xi)N}{\mu+\xi+\nu}, 0, \tfrac{\nu N}{\mu+\xi+\nu}\big)$, threshold
$$\hat\beta^* = \frac{(\mu+\gamma)(\mu+\xi+\nu)}{\mu+\xi},$$
and node–spiral boundaries $\hat\beta_\pm = \big(\hat K \pm 2\sqrt{(\gamma - \nu)A^3}\big)/(\mu+\xi)$, $\hat K = 2(\gamma+\mu)^2 + \xi(4\gamma + 3\mu + \xi - \nu)$.

## Expansion

At $\mathcal O^*$ the Jacobian has eigenvalues $-\mu$, $-(\mu+\xi)$ and $\lambda_3 = \frac{\beta(\mu+\xi-\nu) - (\mu+\gamma)(\mu+\xi)}{\mu+\xi}$, whose sign change gives $\beta^*$; equivalently $\beta^*/(\mu+\gamma) = 1$ is the condition $\mathcal R = \beta S_0^*/((\mu+\gamma)N) = 1$. At the endemic point, besides $-\mu$, the eigenvalues solve $A\lambda^2 + B\lambda + C = 0$ with $B = \beta(\mu+\xi-\nu) + \xi(\mu+\xi)$ and $C = A[\beta(\mu+\xi-\nu) - (\mu+\gamma)(\mu+\xi)]$; the discriminant $B^2 - 4AC$ vanishes exactly at $\beta_\pm$, which separates real (node) from complex (spiral) eigenvalues. (The threshold is written here with denominator $\mu + \xi - \nu$, as forced by $\lambda_3$ and by the positivity condition on $I_E^*$.)

## Sources

- J. Nunuvero, A. Santiago, M. Cohen, A. Radulescu, "Modeling the effects of adherence to vaccination and health protocols in epidemic dynamics by means of an SIR model", arXiv:2308.01038 (2023), Section 2 (model) and Theorems 3.1–3.4 (Section 3), <https://doi.org/10.48550/arXiv.2308.01038>.
