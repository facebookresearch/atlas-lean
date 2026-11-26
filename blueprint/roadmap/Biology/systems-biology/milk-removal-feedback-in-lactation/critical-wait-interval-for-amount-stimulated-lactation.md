# Critical wait interval for amount-stimulated lactation

**Setting.** The state of one breast is the stored milk $m\ge0$ and the production rate $p\ge0$. During a wait interval of length $T>0$,
$$\dot m = p-\delta m,\qquad \dot p=-\gamma p,\qquad \delta,\gamma>0,$$
so that $m(T)=d\,m(0)+G\,p(0)$ and $p(T)=g\,p(0)$ with $g=e^{-\gamma T}$, $d=e^{-\delta T}$, $G=(e^{-\gamma T}-e^{-\delta T})/(\delta-\gamma)$. At a removal session of prescribed duration $\tau$ a fraction $h=\max\{1-\nu\tau,0\}$ of the available milk $x=d\,m+G\,p$ stays behind, the removed amount is $M=x(1-h)$, and production is stimulated by $a(M)$, giving the map
$$F(m,p)=\bigl(x\,h,\ g\,p+a\bigl(x(1-h)\bigr)\bigr),\qquad 0<\tau<\tau_{\mathrm{emp}}:=1/\nu .$$
The stimulation $a\in C^1([0,\infty))$ is strictly increasing and bounded with $a(0)=0$; its efficiency $R(M)=a(M)/M$ is assumed *decreasing* from $R_{\max}=R(0)=a'(0)$ to $0$. Define the efficiency needed to balance production loss over one cycle and its set-duration version,
$$\Gamma(T)=\frac{1-g}{G},\qquad \Gamma_\tau(T)=\frac{\Gamma(T)}{r},\qquad r=\frac{1-h}{1-h\,d}\in(0,1).$$
When $\gamma<R_{\max}$, the *critical wait interval* $T_{\mathrm{crit}}$ solves $\Gamma(T_{\mathrm{crit}})=R_{\max}$, and for $T<T_{\mathrm{crit}}$ the *minimal removal duration* is
$$\tau_{\min}(T)=\tau_{\mathrm{emp}}\,\frac{\Gamma(T)\,(1-d)}{R_{\max}-d\,\Gamma(T)} ,$$
the solution of $\Gamma_{\tau_{\min}}(T)=R_{\max}$.

**Statement.** Let $z_0=(0,0)$ (the involution state).

1. If $T>T_{\mathrm{crit}}$, or $0<T<T_{\mathrm{crit}}$ and $\tau<\tau_{\min}(T)$, then $z_0$ is the unique fixed point of $F$ and it is globally asymptotically stable: lactation ceases under the repeated schedule.
2. If $0<T<T_{\mathrm{crit}}$ and $\tau_{\min}(T)<\tau<\tau_{\mathrm{emp}}$, then $F$ has exactly two fixed points, $z_0$ (unstable) and a lactating state $(m_{\mathrm{lac}},p_{\mathrm{lac}})$ with
$$p_{\mathrm{lac}}=\frac{M_{\mathrm{lac}}}{G\,r},\qquad m_{\mathrm{lac}}=\frac{p_{\mathrm{lac}}\,G\,h}{1-d\,h},$$
where $M_{\mathrm{lac}}$ is the unique root of $R(M)=\Gamma_\tau(T)$; its basin of attraction is the whole state space minus $z_0$.

For Michaelis-Menten stimulation $a(M)=a_{\max}M/(M+\mu_M)$ one gets explicitly $M_{\mathrm{lac}}=\mu_M(\kappa_\tau-1)$ with $\kappa_\tau=R_{\max}/\Gamma_\tau$. If instead $R$ is unimodal (small for small removals), $R(M)=\Gamma_\tau$ has two roots and the model is bistable: lactation persists or ceases depending on the initial state.

## Expansion

A fixed point satisfies $m_*=p_*Gh/(1-dh)$ and $p_*(1-g)=a(p_*Gr)$; writing $M_*=p_*Gr$ for the steady-state removed amount turns this into $R(M_*)=\Gamma_\tau(T)$. Since $R$ decreases from $R_{\max}$ to $0$, a positive root exists exactly when $\Gamma_\tau(T)<R_{\max}$. As $\tau$ increases to $\tau_{\mathrm{emp}}$, $r$ increases to $1$ and $\Gamma_\tau$ decreases to $\Gamma(T)$, and $\Gamma(T)$ increases with $T$ from $\gamma$; so a positive steady state needs $\gamma<R_{\max}$, $T<T_{\mathrm{crit}}$ and $\tau>\tau_{\min}(T)$. Stability follows from monotonicity of the map in the production coordinate: when $R<\Gamma_\tau$ everywhere, each cycle loses more production than it regains and orbits are squeezed to $z_0$; when a lactating root exists, small production levels are amplified ($R(0)>\Gamma_\tau$) and orbits are trapped between $z_0$ and large states and converge to the unique interior fixed point. The feedback is self-reinforcing: falling production lowers the removed amount, which can lower stimulation and accelerate the decline, so beyond $T_{\mathrm{crit}}$ no repeated constant schedule can sustain production.

## Sources

- Angelika Manhart, Tobias Müller, "Milk-removal feedback shapes lactation sustainability and daily output in a model of human lactation", arXiv:2611.33997 (2026), Section "Model" and Section "Model Analysis" (amount-dependent stimulation, set-duration protocol, theorem for decreasing-efficiency responses), <https://doi.org/10.48550/arXiv.2611.33997>
