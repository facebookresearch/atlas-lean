# Discrete-time linear time-invariant control systems and their reachability problem

A discrete-time linear time-invariant (LTI) control system evolves by $x_{t+1} = A x_t + u_t$ with each control $u_t$ taken from a fixed set $U$. Its reachability problem asks whether a given source state can be steered to a given target state in finitely many steps.

**Systems.** An LTI system in dimension $d$ is a pair $\mathcal L = (A, U)$ of a transition matrix $A \in \mathbb Q^{d \times d}$ and a set of controls $U \subseteq \mathbb R^d$. A state $s \in \mathbb R^d$ *can reach* a state $t \in \mathbb R^d$ if there are $T \ge 0$ and controls $u_0, \ldots, u_{T-1} \in U$ such that the solution of

$$
x_{k+1} = A x_k + u_k, \qquad x_0 = s,
$$

satisfies $x_T = t$. The case $T = 0$ is allowed, so every state can reach itself.

**The LTI Reachability Problem.** Given an LTI system $(A, U)$, a source state $s$ and a target state $t$, decide whether $s$ can reach $t$. Variants are distinguished by the class of allowed control sets, given by finite data with rational coefficients: linear or affine subspaces, finite unions of affine subspaces, convex polytopes, sets of the form $V \cup \{0\}$ with $V$ an affine subspace.

## Depends on

- [Discrete-time dynamical system](../../discrete-time-systems-and-safety/discrete-time-dynamical-system.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

An LTI system is the discrete-time dynamical system with state set $\mathbb R^d$, input set $U$ and update map $f(x, u) = A x + u$. When $U$ is a linear subspace, the problem is Harrison's accessibility problem for linear sequential machines, which Kannan and Lipton solved in polynomial time; affine control sets reduce to linear ones by homogenization. Null reachability (can every state be reached from the origin?) and null controllability (can the origin be reached from every state?) are different, universally quantified problems, decidable in polynomial time by linear algebra.

## Sources

- Nathanaël Fijalkow, Joël Ouaknine, Amaury Pouly, João Sousa-Pinto and James Worrell, "On the decidability of reachability in linear time-invariant systems", in *Proceedings of the 22nd ACM International Conference on Hybrid Systems: Computation and Control (HSCC 2019)*, ACM, 2019, pp. 77–86, <https://doi.org/10.1145/3302504.3311796>; read as arXiv:1802.06575v2, <https://arxiv.org/abs/1802.06575v2>: Section 1 (Introduction) of that version, with the definition of LTI systems, reachability and the LTI Reachability Problem, and the discussion of linear and affine control sets.
