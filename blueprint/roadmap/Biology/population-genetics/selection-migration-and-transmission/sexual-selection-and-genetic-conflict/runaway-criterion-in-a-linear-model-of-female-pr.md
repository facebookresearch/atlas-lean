# Stability and runaway in a linear preference–trait model

Let $G>0$, $a>0$, $\omega>0$, $B,\theta\in\mathbb R$ be fixed.
For real trait and preference means $z_t,y_t$, define the discrete linear
model

$$\binom{z_{t+1}-z_t}{y_{t+1}-y_t}
 =\tfrac12\binom GB u_t,\qquad
 u_t=ay_t-(z_t-\theta)/\omega^2,\qquad
 \lambda=1+\tfrac12(aB-G/\omega^2).$$

Every equilibrium lies on $u=0$, every increment is parallel to $(G,B)$,
and exactly $u_t=\lambda^tu_0$. For $\lambda\ne1$,

$$\binom{z_t}{y_t}=\binom{z_0}{y_0}
 +\tfrac12\binom GB u_0\frac{1-\lambda^t}{1-\lambda}.$$

Consequently, $|\lambda|<1$, equivalently $0<G/\omega^2-aB<4$, gives
convergence to the initial-state-dependent point on the equilibrium line
obtained by replacing $\lambda^t$ by zero. If $|\lambda|>1$ and $u_0\ne0$,
then $|u_t|$ and $|z_t|$ diverge; $|y_t|$ also diverges if $B\ne0$.
If $B/G>1/(a\omega^2)$, then $\lambda>1$ and $B>0$, so the two means
run away in the same direction for $u_0\ne0$. This is not the only
instability: $\lambda<-1$ gives alternating divergence.

If $u_0=0$, the state is fixed for every parameter choice.
For $\lambda=1$ and $u_0\ne0$, $u_t$ is constant but the means drift
linearly. For $\lambda=-1$ and $u_0\ne0$, the state is a nontrivial
two-cycle. The unsigned distance to the line is multiplied by
$|\lambda|$, not by a possibly negative $\lambda$.

## Expansion

Apply the linear functional defining $u$ to the update to obtain
$u_{t+1}=\lambda u_t$, then sum the geometric increments. Since $G>0$,
$u=0$ is necessary and sufficient for an equilibrium. These identities
also prove the equality cases. The model can be interpreted as a fixed
trait variance $G$ and covariance $B$ under male-only selection, with the
factor one half accounting for selection in one sex. Any biological
covariance model must separately choose a preference variance making its
covariance matrix positive semidefinite. The stated system itself is a
linear model on real means, so its divergence is global; a nonlinear or
state-dependent-variance model gets no global conclusion from this test.

## Sources

- R. Lande, "Models of speciation by sexual selection on polygenic traits", PNAS 78 (1981), 3721--3725, <https://doi.org/10.1073/pnas.78.6.3721>, abstract (runaway depending on genetic parameters and initial state, and lines of equilibria). The exact discrete linear model and all case distinctions above are derived here.
