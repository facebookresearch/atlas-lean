# ε-regularity criterion for one-dimensional quasilinear Keller–Segel systems

**Setting.** Let $m \in \mathbb{R}$, $\tau, k \in \{0,1\}$ with $(\tau,k) \in \{(0,0),(0,1),(1,1)\}$ (Jäger–Luckhaus, parabolic–elliptic and fully parabolic settings), and consider on $(0,1)\times(0,T)$ with homogeneous Neumann conditions
$$u_t = \big(D(u)u_x - S(u)v_x\big)_x, \qquad \tau v_t = v_{xx} - k v - (1-k)M + u,$$
where $D(\sigma) = (\sigma+1)^{m-1}$, $S(\sigma) = \sigma(\sigma+1)^m$ for $\sigma \ge 0$, and $M = \int_0^1 u_0$. The ratio $S(u)/D(u) \sim u^2$ for large $u$, which is the critical growth $u^{2/n}$ for $n = 1$. Initial data satisfy $u_0, \tau v_0 \in \bigcup_{\theta>1} W^{1,\theta}((0,1))$, $0 \not\equiv u_0 \ge 0$, $\tau v_0 \ge 0$.

**Theorem (local existence and ε-regularity).** For all such data there is a unique nonnegative classical solution on a maximal interval $[0, T_{\max})$, with $\limsup_{t \nearrow T_{\max}} \|u(\cdot,t)\|_{L^\infty} = \infty$ if $T_{\max} < \infty$; the mass $\int_0^1 u(\cdot,t) = M$ is conserved. Moreover there is $\varepsilon > 0$ (independent of the data) such that, if for some $\delta > 0$
$$\int_a^b u(\cdot,t) < \varepsilon \quad \text{for all } t \in (0,T_{\max}) \text{ whenever } 0 \le a \le b \le 1,\ |b-a| \le \delta,$$
then $u$ is bounded in $(0,1)\times(0,T_{\max})$ and hence $T_{\max} = \infty$.

**Sufficient conditions.** The hypothesis above holds (for every $\varepsilon > 0$ and suitable $\delta$) if any of the following holds: the family $\{u(\cdot,t)\}_{t < T_{\max}}$ is uniformly integrable on $(0,1)$; $\sup_t \int_0^1 \Phi(u(\cdot,t)) < \infty$ for some continuous $\Phi \ge 0$ with $\Phi(\xi)/\xi \to \infty$; or the mass accumulation function $w(x,t) = \int_0^x u(\rho,t)\,d\rho$ is uniformly continuous in $x$ uniformly in $t$.

## Expansion

The key tool is a one-dimensional interpolation inequality: for $\alpha > 2$ and $\eta > 0$ there is $\varepsilon > 0$ such that, for every $\delta > 0$, functions $\varphi$ with small mass on all intervals of length less than $\delta$ satisfy $\int_0^1 |\varphi|^\alpha \le \eta \int_0^1 |(|\varphi|^{(\alpha-2)/2})_x|^2 + C(\delta)$. Testing the first equation with $(u+1)^{p-1}$-type weights and controlling $v_{xx}$ by maximal Sobolev regularity, the cross-diffusive contribution is absorbed into the diffusion, giving uniform $L^p$ bounds for every $p > \max\{1, 1-m\}$, from which an $L^\infty$ bound follows. Concentration of mass at a point is therefore the only possible blow-up mechanism.

## Sources

- X. Cao and M. Fuest, "Absence of critical mass phenomena in one-dimensional critical quasilinear Keller–Segel systems", arXiv:2606.18006 (2026), Proposition 1.1, Lemma 2.2, Lemma 2.4 and Proposition 2.5, <https://doi.org/10.48550/arXiv.2606.18006>.
