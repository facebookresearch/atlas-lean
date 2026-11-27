# Fast collapse threshold and entry–exit map in the Bazykin–Berezovskaya model

**Model.** Prey (resource) $u\in[0,1]$ and predator (production) $v\ge0$ evolve by

$$\dot u=-uv+\varepsilon\,u(u-l)(1-u),\qquad \dot v=-\gamma v(m-u),$$

with Allee threshold $0<l<1$, predator break-even prey level $m>0$, conversion ratio $\gamma>0$ and $0<\varepsilon\ll1$: predation is fast, prey growth slow. The critical manifold is the prey axis $\mathcal C_0=\{v=0\}$, attracting where $u<m$ and repelling where $u>m$.

**Fast subsystem ($\varepsilon=0$).** $\dot u=-uv$, $\dot v=-\gamma v(m-u)$, the susceptible–infected part of an SIR model with $m^{-1}$ playing the role of $R_0$.
- (Proposition 1) Every trajectory converges to $\mathcal C_0$.
- (Proposition 2) $\Gamma(u,v)=m\log u-u-v/\gamma$ is a constant of motion, and the limit prey level satisfies $u_\infty\in(0,m)$.
- (Proposition 3) Assume $m>l$ and start $\mathcal O(1)$ away from $\mathcal C_0$. Then the fast predation phase drives the prey below the Allee threshold, $u_\infty\le l$, if and only if $v_0\ge\alpha(u_0)$, where $\alpha(u)=\gamma\big(m\log(u/l)-u+l\big)$ is the level curve of $\Gamma$ through $(l,0)$. If $m<(l-1)/\log l$, $\alpha$ is positive exactly on $(l,\tilde u)$ with $\tilde u\in(m,1)$ its unique zero there; if $m>(l-1)/\log l$, $\alpha>0$ exactly for $u_0>l$.

**Entry–exit relation.** For $l<m<1$, an orbit that lands on $\mathcal C_0$ at $u_\infty\in(l,m)$ drifts slowly toward $u=1$, crosses into the repelling part, and leaves $\mathcal C_0$ at the exit point $u_E\in(m,1)$ determined to leading order by

$$l(1-m)\log\frac{1-u_E}{1-u_\infty}+m(l-1)\log\frac{u_E}{u_\infty}+(m-l)\log\frac{u_E-l}{u_\infty-l}=0,$$

the vanishing of the accumulated fast eigenvalue $\int_0^{\tau_E}-\gamma(m-u(\tau))\,d\tau$ along the slow flow. As $u_\infty\to l^+$, $u_E\to1^-$.

## Expansion

Since $\dot u\le0$ and $\dot u+\dot v/\gamma\le0$, both coordinates have limits, and integrability forces $v_\infty=0$; differentiating $\Gamma$ along the flow gives $m\dot u/u-\dot u-\dot v/\gamma=-mv+uv+v(m-u)=0$. Setting $\Gamma(u_0,v_0)=\Gamma(u_\infty,0)$ makes $u_\infty$ a monotone function of $v_0$, and $u_\infty=l$ defines the separatrix $v_0=\alpha(u_0)$: above it the predator overshoots and drives the prey into the Allee trap, after which the slow flow takes $u$ to $0$. Below it, the prey recovers slowly toward its carrying capacity and the entry–exit map $u_\infty\mapsto u_E$ combined with the fast map back to $\mathcal C_0$ yields a return map whose fixed points correspond to relaxation oscillations. Fenichel theory (Theorem 1) covers the normally hyperbolic parts of $\mathcal C_0$ away from $u=m$, and the entry–exit function handles the passage through that non-hyperbolic point.

## Sources

- J. Borsotti, M. Sensi, "A geometric analysis of the Bazykin-Berezovskaya predator-prey model with Allee effect in an economic framework", *Nonlinear Analysis: Real World Applications* 89 (2026), 104534, Theorem 1 (Fenichel), Propositions 1–3 and the entry–exit relation of Section 3, <https://doi.org/10.1016/j.nonrwa.2025.104534> (preprint arXiv:2504.10355).
