# Sampling a continuous-time flow into discrete dynamics

Let a continuous-time system with inputs held constant on each sampling interval (zero-order hold) have a flow
$\phi_t(x, u)$, assumed to exist and be unique on the domain considered (for example by the Picard–Lindelöf theorem under a
Lipschitz vector field; this is a hypothesis, not proved here). For a sampling period $h > 0$, the sampled system is the
discrete system $f_h(x, u) = \phi_h(x, u)$ on the state-input pairs for which the held-input solution exists on $[0, h]$; it is a
total update map only when that solution exists for every pair, and is undefined elsewhere. With states in a normed space (for example $\mathbb{R}^n$), a one-step method is a family $\Psi_h$ of discrete systems; its local defect at
$(x, u)$ is $\lVert \Psi_h(x, u) - \phi_h(x, u) \rVert$. For a set $K$ of state-input pairs, an order $p \in \mathbb{N}$ and $h_0 > 0$, the
method is consistent of order $p$ on $K$ if there is $C \ge 0$ with $\lVert \Psi_h(x,u) - \phi_h(x,u) \rVert \le C h^{p+1}$ for all
$0 < h \le h_0$ and $(x, u) \in K$. The specialization of this bound to sampled trajectories staying in $K$ is a separate lemma;
convergence from consistency and stability is a separate theorem.

## Depends on

- [Discrete-time dynamical system (input-driven state-update map)](discrete-time-dynamical-system.md)

## Related topics

- [Zero-order-hold sampling of a linear time-invariant system](../sampled-data-systems/zero-order-hold-sampled-system.md)

## Sources

- Mathematical Control Theory: Deterministic Finite Dimensional Systems, 2nd ed. — E. D. Sontag, Springer, 1998. <http://www.sontaglab.org/FTPDIR/sontag_mathematical_control_theory_springer98.pdf> Section 2.10, Definition 2.10.1 (p. 72): the $\delta$-sampled system, undefined where the solution does not exist on the whole sampling interval. The local
  defect and the order of consistency are defined here directly.
