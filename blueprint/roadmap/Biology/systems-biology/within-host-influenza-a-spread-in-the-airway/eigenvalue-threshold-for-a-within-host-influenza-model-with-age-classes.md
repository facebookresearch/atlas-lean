# Eigenvalue threshold for a within-host influenza A model with infectious age classes

**Model.** Along the airway coordinate $x$, uninfected target cells $T$, eclipse-phase cells $E_1,\dots,E_{n_E}$, productively infected cells $I_1,\dots,I_{n_I}$ (Erlang-distributed stages) and free virus $V$ evolve by
$$\partial_tT=-\beta TV,\qquad \partial_tE_1=\beta TV-c_EE_1,\qquad \partial_tE_i=c_EE_{i-1}-c_EE_i,$$
$$\partial_tI_1=c_EE_{n_E}-c_II_1,\qquad \partial_tI_j=c_II_{j-1}-c_II_j,\qquad \partial_tV=p\sum_{j=1}^{n_I}I_j-cV+D_{PCF}\,a+v_aW,\qquad \partial_xV=W,$$
with $c_E=n_E/\tau_E$, $c_I=n_I/\tau_I$ (mean eclipse and infectious durations $\tau_E,\tau_I$), infection rate $\beta$, virion production $p$, clearance $c$, mucociliary transport $v_a$, and the diffusion term $\partial_{xx}V$ replaced by a constant $a$.

**Definition.** With $T$ treated as a parameter, call the system *definite* if $c>\tau_Ip\beta T$ and *indefinite* if $c<\tau_Ip\beta T$. Note that $\tau_Ip\beta T/c$ is the number of new infected cells produced by one infected cell (virions produced over the infectious period, $p\tau_I$, times infections per virion, $\beta T/c$).

**Proposition.** Let $n_E=0$. For the matrix $A$ of the linear part of the vector field in $(I_1,\dots,I_{n_I},V,W)$, the characteristic polynomial satisfies
$$(-1)^{n_I}\det(A-\lambda I)=(c_I+\lambda)^{n_I}(c+\lambda)\lambda+\beta Tp\big(c_I^{n_I}-(c_I+\lambda)^{n_I}\big).$$
Zero is always an eigenvalue. If the system is definite, all nonzero real eigenvalues are negative; if it is indefinite, there is exactly one positive eigenvalue and all other nonzero real eigenvalues are negative. Every real eigenvalue has geometric multiplicity one, and its eigenvector is explicit: for $\lambda\ne0$ it is proportional to $\big(\tfrac{\beta T}{c_I+\lambda},\tfrac{c_I\beta T}{(c_I+\lambda)^2},\dots,\tfrac{c_I^{n_I-1}\beta T}{(c_I+\lambda)^{n_I}},1,0\big)$.

So the sign change of the dominant eigenvalue occurs at the target-cell level $T=c/(\tau_Ip\beta)$, the within-host analogue of a reproduction-number threshold.

## Expansion

Expanding the determinant along the cyclic chain $V\to I_1\to\cdots\to I_{n_I}\to V$ gives the stated polynomial. Dividing by $\lambda$, the remaining factor at $\lambda=0$ equals $c_I^{n_I}c-\beta Tp\,n_Ic_I^{n_I-1}=c_I^{n_I}(c-\tau_Ip\beta T)$, so its sign is set by definiteness, and Descartes' rule of signs on the real polynomial gives either no or exactly one positive root. Because each stage feeds only the next, the eigenspace of each real eigenvalue is one-dimensional.

## Sources

- Boldizsár Kalmár, "Some approximate solutions to the spread of influenza A virus infection", arXiv:2110.02790 (2021), Corollary 2.2, the definite/indefinite definition and Propositions 3.2–3.4, Corollary 3.5, <https://doi.org/10.48550/arXiv.2110.02790>.
