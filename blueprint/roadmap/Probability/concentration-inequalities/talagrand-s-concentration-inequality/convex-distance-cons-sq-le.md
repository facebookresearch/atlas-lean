# Talagrand's geometric step

For $A \subseteq \Omega^{N+1}$, $\omega \in \Omega$, $x \in \Omega^N$ and $0 \le \lambda \le 1$,

$$f_c^2(A, (\omega, x)) \le (1 - \lambda)^2 + \lambda\, f_c^2(A(\omega), x) + (1 - \lambda)\, f_c^2(B, x),$$

where $A(\omega)$ is the section and $B$ the projection (Talagrand, *Concentration of measure and
isoperimetric inequalities in product spaces*, Publ. Math. IHÉS 81 (1995), (4.1.7)). If
$s \in U_{A(\omega)}(x)$ then $(0, s) \in U_A((\omega, x))$, and if $t \in U_B(x)$ then
$(1, t) \in U_A((\omega, x))$; so $(\lambda s + (1-\lambda) t, 1 - \lambda)$ lies in the convex hull,
and convexity of $u \mapsto u^2$ gives the bound. Talagrand splits off the last coordinate; the
first is used here.

The projection must be nonempty, and the section too unless $\lambda = 0$: the distance to
an empty set is taken to be $0$, not $+\infty$.
