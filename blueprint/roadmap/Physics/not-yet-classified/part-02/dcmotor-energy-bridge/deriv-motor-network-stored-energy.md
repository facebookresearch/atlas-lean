# Storage balance of the DC motor network loop

Let $R \ge 0$, $L > 0$ and $k_e$ be real, and let $u, i, \omega : \mathbb{R} \to \mathbb{R}$ be the terminal voltage, armature current and rotor speed. Embed the motor as a series loop of a supply source, an armature resistance $R$, an armature inductance $L$ and a back-EMF source $k_e\omega$, with branch voltages obtained from the node potentials $(u,\ u - R i,\ k_e\omega)$ through the loop incidence matrix and the same current $i$ in every branch. The network stored energy of the loop is then $E(s) = \tfrac12 L\, i(s)^2$. If $i$ is differentiable at $t$ and the armature equation

$$u(t) = R\, i(t) + L\, i'(t) + k_e\, \omega(t)$$

holds at $t$, then

$$E'(t) = u(t)\, i(t) - R\, i(t)^2 - k_e\, \omega(t)\, i(t).$$
