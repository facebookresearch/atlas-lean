# Strang's first lemma, infimum form

Let $E$ and $V$ be real inner product spaces and $J : V \to E$ a linear isometry. Let $B$ be a
bounded bilinear form and $\ell$ a bounded linear functional on $E$, and $B_h$, $\ell_h$ the same on
$V$, with $\alpha > 0$ such that $\alpha \|v\|^2 \le B_h(v, v)$ for every $v \in V$. Let $u \in E$
satisfy $B(u, w) = \ell(w)$ for all $w \in E$, and $u_h \in V$ satisfy $B_h(u_h, w) = \ell_h(w)$ for
all $w \in V$. Write $\delta_B = \|B_h - B(J\cdot, J\cdot)\|$ and $\delta_\ell = \|\ell_h - \ell \circ J\|$.
Then

$$\|u - J u_h\| \le \Big(1 + \frac{\|B\| + \delta_B}{\alpha}\Big) \inf_{v_h \in V} \|u - J v_h\| + \frac{\delta_\ell + \delta_B\, \|u\|}{\alpha} .$$
