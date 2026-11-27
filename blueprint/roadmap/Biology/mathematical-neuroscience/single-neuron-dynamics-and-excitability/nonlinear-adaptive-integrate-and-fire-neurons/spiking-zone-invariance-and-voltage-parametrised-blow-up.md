# Spiking zone invariance and voltage-parametrised blow-up in nonlinear adaptive integrate-and-fire neurons

**Model.** The nonlinear bidimensional integrate-and-fire neuron (adaptive exponential, quartic and related models) has membrane potential $v$ and adaptation variable $w$ with

$$\dot v = F(v) - w + I(t), \qquad \dot w = a(bv - w), \qquad a, b \ge 0,$$

where $F$ is $C^3$, strictly convex, $\lim_{x\to-\infty}F'(x) \le 0$, and $F(v) \ge \alpha v^{1+\varepsilon}$ for large $v$ (some $\alpha, \varepsilon > 0$). A spike is the finite-time blow-up of $v$ (or crossing of a cutoff $\theta$), after which $(v,w) \mapsto (v_r, w + d)$. If moreover $F(v) \ge \alpha v^{2+\varepsilon}$, $w$ stays bounded at the blow-up time, so the reset value $w + d$ is well defined.

**Definition.** If $I(t) \ge I^*$ on $(\tau_0, \tau_1)$, let $Z^* = Z(I^*, b) = \{(v, w) : v > v_+(I^*, b),\ w \le bv\}$, where $v_+(I^*, b)$ is the largest fixed point of the system with constant input $I^*$ ($-\infty$ if there is none, i.e. if $I^* > -m(b)$ with $m(b) = \min_v (F(v) - bv)$). The inequality $v > v_+$ is strict: this corrects Definition 1 of the source (used in its Lemma 1 and Theorem 2), which prints $Z^*:=Z(I^*,b)=\cup_{V \geq v_+(I^*,b)} Z(V)$ with $Z(V)=\{(v,w) \in \mathbb R^2 : v \geq V \text{ and } w \leq b\,v\}$. That set contains $(v_+, bv_+)$, an equilibrium when $I \equiv I^*$; for example with $F(v) = v^2$, $a = b = 1$ and $I \equiv I^* = 0$ one has $v_+ = 1$, and the solution from $(1, 1)$ is constant, with no blow-up.

**Theorem.** Assume $I(t) \ge I^*$ on $(\tau_0, \tau_1)$.
1. $Z^*$ is positively invariant under the flow.
2. For $(v_0, w_0) \in Z^*$ the solution has $\dot v > 0$, so $t \mapsto v(t)$ is smoothly invertible; its inverse $T(v)$ and $W(v) = w(T(v))$ solve

$$\frac{dT}{dv} = \frac{1}{F(v) - W + I(T)}, \qquad \frac{dW}{dv} = \frac{a(bv - W)}{F(v) - W + I(T)},$$

and the spike (explosion) time and the adaptation value at the spike are $\lim_{v\to\infty}T(v)$ and $\lim_{v\to\infty}W(v)$.
3. *Explicit Euler.* If $(v_0, w_0) \in Z^*$ and the step $\tau$ satisfies $\tau a < 1$, the Euler iterates stay in $Z^*$, $v_n$ and $w_n$ increase strictly, and $v_n \to \infty$ without finite-step blow-up, so fixed-step schemes misplace spike times and the post-spike adaptation value.

## Proof sketch

On the boundary line $w = bv$ of $Z^*$, $\frac{d}{dt}(w - bv) = -b(F(v) - bv + I(t)) \le -b(F(v) - bv + I^*) < 0$ for $v$ beyond the largest fixed point, so trajectories cannot leave; inside $Z^*$, $\dot v = F(v) - w + I \ge F(v) - bv + I^* > 0$. Using $v$ as the independent variable removes the singularity: the right-hand sides of the $(T, W)$ system decay like $1/F(v)$, which is integrable, so both limits are finite and computable to fixed precision by integrating in $v$. This yields a hybrid algorithm: a time-stepped Euler scheme away from the $v$-nullcline, switched to integration in $v$ inside the spiking zone, with step sizes chosen to guarantee a prescribed error on $w$ at the cutoff.

## Sources

- Jonathan Touboul, "On the Simulation of Nonlinear Bidimensional Spiking Neuron Models", *Neural Computation* 23 (2011), 1704–1742, <https://doi.org/10.1162/neco_a_00141>. Preprint version: arXiv:1008.1954 (2010), Sections 2, 3 and 5 (definition of the spiking zone, Euler monotonicity lemma, blow-up theorem in voltage parametrisation), <https://doi.org/10.48550/arXiv.1008.1954>.
