# Loop-breaking criterion for marginally stable equilibria

**Setting.** Consider a parameter-dependent biochemical network $\dot x=F(x,p)$, $x\in\mathbb R^n$, $p\in\mathcal P\subset\mathbb R^m$, and let $\mathcal M$ be the set of equilibrium–parameter pairs $\xi=(x^*,p)$. A *loop breaking* is a pair $(f,h)$ with $F(x,p)=f(x,h(x),p)$: cutting a feedback circuit turns the system into an open-loop system $\dot x=f(x,u,p)$, $y=h(x)$. Linearizing at $\xi$ gives $(A(\xi),B(\xi),C(\xi))$ with closed-loop Jacobian $A+BC$ and open-loop transfer function

$$G(\xi,s)=C(\xi)(sI-A(\xi))^{-1}B(\xi)=\frac{k(\xi)q(\xi,s)}{r(\xi,s)}.$$

A *critical frequency* is $\omega_c\in\mathbb R$ with $G(\xi,j\omega_c)\in\mathbb R$; let $\Omega_c(\xi)$ be their set. Assume (A1): for $\xi\in\mathcal M$, $G(\xi,\cdot)$ has no poles or zeros on the imaginary axis, and the degrees of $q(\xi,s)$ and $r(\xi,s)$ in $s$ are constant on $\mathcal M$. With $p_\pm$ ($z_\pm$) the numbers of poles (zeros) of $G$ in the right/left half-plane, $\alpha=|p_+-p_-+z_--z_+|$ is constant on $\mathcal M$.

**Propositions.** A point $s_0$ that is not an open-loop eigenvalue is a closed-loop eigenvalue iff $G(\xi,s_0)=1$. Under (A1), $0\in\Omega_c(\xi)$, $\Omega_c$ is symmetric, and if $j\omega_c$ is a closed-loop eigenvalue then $\omega_c\in\Omega_c(\xi)$; moreover $\Omega_c(\xi)$ has at least $\tilde\alpha$ elements, $\tilde\alpha=\alpha$ if $\alpha$ is odd and $\alpha-1$ if even (it is *minimal* if it has exactly $\tilde\alpha$).

**Theorem (topological equivalence).** Under (A1), two hyperbolic pairs $\xi_1,\xi_2$ with minimal $\Omega_c$ have Jacobians with the same numbers of stable and unstable eigenvalues iff $\beta(\xi_1)=\beta(\xi_2)$, where $\beta(\xi)=\#\{\omega_c\in\Omega_c(\xi):G(\xi,j\omega_c)>1\}$.

**Theorem (existence of a bifurcation point).** Under (A1) and (A2) ($\Omega_c(\xi)$ minimal on $\mathcal M$, with consistently labelled critical frequencies $\omega^i_c$), there is $\xi_c\in\mathcal M$ whose Jacobian has an eigenvalue on the imaginary axis iff there are $\xi_1,\xi_2\in\mathcal M$ and an index $i\le\tilde\alpha$ with

$$G(\xi_1,j\omega^i_c(\xi_1))\le1\le G(\xi_2,j\omega^i_c(\xi_2)).$$

A crossing at the zero critical frequency generically gives a saddle-node bifurcation, and one at a nonzero critical frequency a Hopf bifurcation.

## Expansion

This is a Nyquist-type argument: closed-loop eigenvalues on the imaginary axis are points where the open-loop frequency response crosses the real value $1$, and since $G(\xi,j\omega)$ is real exactly at the critical frequencies, the stability type of the equilibrium is encoded by how many of the real values $G(\xi,j\omega_c)$ exceed one. By continuity along a path in $\mathcal M$, a sign change of $G(\xi,j\omega^i_c(\xi))-1$ forces a crossing. This turns the search for bifurcations in a high-dimensional parameter space into a scalar optimization: maximize or minimize $G(\xi,j\omega^i_c(\xi))$ over sampled parameters to bracket the value $1$, then refine. Applied to a MAPK cascade with negative feedback, the method locates Hopf bifurcations giving sustained oscillations.

## Sources

- Steffen Waldherr and Frank Allgöwer, "Searching bifurcations in high-dimensional parameter space via a feedback loop breaking approach", International Journal of Systems Science 40 (2009), 769–782, <https://doi.org/10.1080/00207720902957269>; numbering as in arXiv:0812.0256: Section 2 (Definitions 1–4, Propositions 1–4, eigenvalue lemma, assumption (A1)) and Section 3 (assumption (A2), Theorems 1 and 2, search algorithm).
