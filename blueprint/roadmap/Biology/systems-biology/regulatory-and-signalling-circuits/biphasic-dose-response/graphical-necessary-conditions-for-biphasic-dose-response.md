# Graphical necessary conditions for biphasic dose response

**Setting.** Consider $\dot{\mathbf x}=\mathbf f(\mathbf x)+\hat{\mathbf e}_1g(u)$ on $\mathcal X\subset\mathbb R^n$ with output $y=x_j$, where $\mathbf f\in C^1$, every Jacobian entry $\partial f_i/\partial x_k$ has a constant sign on $\mathcal X$, $\partial f_i/\partial x_i<0$, and $\partial_ug\ne0$ has constant sign; the input $u$ acts only on $x_1$. Assumption (A0): for every $u_0$ there is a steady state with invertible Jacobian, so steady-state curves $\mathbf x^*(u)$ exist by the implicit function theorem. Assumption (A1): additionally these steady states are Hurwitz and globally attracting for nearby $u$. The *J-graph* $G$ has a signed edge $k\to i$ whenever $\partial f_i/\partial x_k\ne0$. The system is *quasi-adaptive* if $\partial_ux_j^*(u_0)=0$ for some $u_0$, and *biphasic* if $\partial_ux_j^*$ takes both signs. PFBL/NFBL denote positive/negative feedback loops, IFFL an incoherent feedforward loop (two oppositely signed paths), and an I/O path is a directed path from $x_1$ to $x_j$.

**Theorem 3.5 (output at the input node).** Under (A0) with output $x_1$, if $G$ has no PFBL disjoint from $x_1$, the system cannot be quasi-adaptive nor biphasic.

**Theorem 3.6 (output elsewhere).** Under (A0) with output $x_j$, $j\ne1$: if $G$ has no I/O path, $x_j^*(u)$ does not depend on $u$; if there is an I/O path but neither an IFFL from $x_1$ to $x_j$ nor a PFBL vertex-disjoint from some I/O path, the system cannot be quasi-adaptive nor biphasic.

**Theorem 3.10 (stable branches).** Under (A1), on a stable branch $\mathbf x^*(u)$: with output $x_1$, if no NFBL is reachable both to and from $x_1$, then $x_1^*(u)$ is monotone; with output $x_j\ne x_1$, if there is neither an IFFL from $x_1$ to $x_j$ nor an NFBL reachable from $x_1$ and reaching $x_j$, then $x_j^*(u)$ is monotone.

**Corollary 3.11.** Under (A1), stable biphasic response requires, for output $x_1$, both a PFBL disjoint from $x_1$ and an NFBL reachable to and from $x_1$; for output $x_j\ne x_1$, either an IFFL from $x_1$ to $x_j$, or a PFBL vertex-disjoint from some I/O path together with an NFBL reachable from $x_1$ and reaching $x_j$. Corollary 4.2 extends these conditions to activation/inhibition inputs $g(u,x_1)=u(T_1-x_1)$, and Theorem 5.1 applies them to a kinetic proofreading model of T-cell activation.

## Expansion

Differentiating $\mathbf f(\mathbf x^*(u))+\hat{\mathbf e}_1g(u)=0$ gives $\partial_u\mathbf x^*=-J^{-1}\hat{\mathbf e}_1\partial_ug$, so by Cramer's rule $\partial_ux_j^*$ is proportional to the minor $J[\hat1,\hat j]$ divided by $\det J$. If the symbolic minor is a polynomial in the Jacobian entries with no mixed signs, it can never vanish and quasi-adaptation and biphasic response are impossible. A principal minor $J[\gamma]$ has mixed signs iff the induced subgraph on $\gamma$ contains a positive feedback loop, and a non-principal minor $J[\hat1,\hat j]$ expands over I/O paths times cycle covers of the remaining nodes, which produces the IFFL and disjoint-PFBL conditions. For stable branches, the sign of $\det J$ is fixed and walks from input to output all share a sign unless an IFFL or a reachable NFBL exists, which yields monotone transients and monotone steady states.

## Sources

- P. Y. Yu, E. D. Sontag, "A necessary condition for nonmonotonic dose response, with an application to a kinetic proofreading model", *2024 IEEE 63rd Conference on Decision and Control (CDC)* (2024), 4823–4829, Theorems 3.5, 3.6, 3.10, 5.1 and Corollaries 3.11, 4.2, <https://doi.org/10.1109/cdc56724.2024.10886687> (preprint arXiv:2403.13862).
