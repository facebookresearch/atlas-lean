# Incremental small-gain theorem

Let $X$ be a Banach space and let $G, K : X \to X$ be maps, not necessarily linear, that are Lipschitz with constants $\gamma_G$ and $\gamma_K$: $\|G(x) - G(x')\| \le \gamma_G\|x - x'\|$, and likewise for $K$. If $\gamma_G\gamma_K < 1$, then for every reference $r \in X$ the feedback equations

$$e = r - K(y), \qquad y = G(e)$$

have exactly one solution $(e, y)$, and the closed-loop maps $r \mapsto e$ and $r \mapsto y$ are Lipschitz with constants $1/(1 - \gamma_G\gamma_K)$ and $\gamma_G/(1 - \gamma_G\gamma_K)$. If, in addition, $X$ carries truncations $P_t$ as in the linear small-gain page, and $G$ and $K$ are causal ($P_t G = P_t G P_t$), then the closed-loop maps are causal.

A bound on the gain at zero alone, $\|G(x)\| \le \gamma\|x\|$, does not give uniqueness or continuity of the closed loop for nonlinear $G$; the incremental (Lipschitz) gain is what the argument uses. For linear $G$ and $K$ the two notions coincide with the operator norms.

**Proof.** The error $e$ must be a fixed point of $\Phi_r(e) = r - K(G(e))$. Since $\|\Phi_r(e) - \Phi_r(e')\| \le \gamma_K\gamma_G\|e - e'\|$, $\Phi_r$ is a contraction of the complete space $X$, and Banach's fixed-point theorem gives a unique fixed point $e(r)$, with $y = G(e(r))$. For two references, $\|e(r) - e(r')\| \le \|r - r'\| + \gamma_K\gamma_G\|e(r) - e(r')\|$, which gives the first Lipschitz constant, and the second follows from that of $G$. For causality, if $P_t r = P_t r'$ then the iterates $e_{k+1} = \Phi_r(e_k)$ and $e'_{k+1} = \Phi_{r'}(e'_k)$ started from $0$ satisfy $P_t e_k = P_t e'_k$ by induction, since $P_t K G = P_t K P_t G P_t$; passing to the limit gives $P_t e(r) = P_t e(r')$.

## Background

- [Small-gain inverse for causal bounded operators](small-gain-inverse-for-causal-bounded-operators.md): the linear case, with the Neumann-series inverse

## Sources

- K. J. Åström and R. M. Murray, *Feedback Systems: An Introduction for Scientists and Engineers*, 2nd ed., Princeton University Press, 2021 (electronic edition v3.0i, <http://fbsbook.org>), Section 10.5, Theorem 10.4 (small gain theorem, p. 10-24): a feedback interconnection of input/output stable systems with gains $\gamma_1\gamma_2 < 1$ is input/output stable with gain $\gamma_1/(1 - \gamma_1\gamma_2)$. The incremental version with existence, uniqueness and causality of the closed loop by the contraction principle is derived on the page.
