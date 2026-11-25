# State-space form of the zone thermal network

Let $\iota$ be a finite set of zones with capacities $C_i > 0$, real conductances $G_{ij}$ and outdoor conductances $g_{0,i}$, zone temperatures $T_i(t)$, outdoor temperature $T_{\mathrm{out}}(t)$ and heating powers $P_i(t)$. Set

$$\mathbf A = \operatorname{diag}(1/C)\Big(G - \operatorname{diag}\big(\textstyle\sum_j G_{ij} + g_{0,i}\big)\Big), \qquad \mathbf B = \operatorname{diag}(1/C)\,[\,g_0 \mid I\,],$$

with input $w(t) = (T_{\mathrm{out}}(t), P(t))$. Then $T$ is differentiable at every $t$ with $T'(t) = \mathbf A T(t) + \mathbf B w(t)$ if and only if, at every $t$ and in every zone $i$, $T_i$ is differentiable at $t$ with

$$C_i T_i'(t) = \sum_j G_{ij}\big(T_j(t) - T_i(t)\big) + g_{0,i}\big(T_{\mathrm{out}}(t) - T_i(t)\big) + P_i(t).$$

No sign or symmetry condition on $G$ or $g_0$ is needed.
