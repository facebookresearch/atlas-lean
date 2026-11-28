# Reachability in LTI systems with finite unions of affine control subspaces is undecidable

Reachability between two states of a discrete-time linear time-invariant control system is undecidable when the set of controls may be a finite union of affine subspaces, although it is decidable in polynomial time when the set of controls is a single affine subspace.

**Theorem (Fijalkow, Ouaknine, Pouly, Sousa-Pinto and Worrell).** The [LTI Reachability Problem](discrete-time-lti-control-systems.md) is undecidable for LTI systems whose sets of controls are finite unions of affine subspaces: no algorithm decides, given $d$, a rational matrix $A \in \mathbb Q^{d \times d}$, a set of controls $U \subseteq \mathbb R^d$ given as a finite union of affine subspaces (by rational data), and states $s, t \in \mathbb Q^d$, whether $s$ can reach $t$ in the system $x_{k+1} = A x_k + u_k$, $u_k \in U$.

The dimension $d$ and the number of affine subspaces are part of the input. For a single affine subspace (in particular a linear subspace) the problem is decidable in polynomial time (Kannan and Lipton).

## Depends on

- [Discrete-time linear time-invariant control systems and their reachability problem](discrete-time-lti-control-systems.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Davis–Putnam–Robinson–Matiyasevich theorem](../../../../TheoryOfComputation/undecidable-problems/diophantine-sets-and-hilbert-s-tenth-problem/dprm-theorem.md)
- [Halting is undecidable](../../../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The proof reduces the vector reachability problem for invertible matrices: given invertible $A_1, \ldots, A_k \in \mathbb Q^{d \times d}$ and $x, y \in \mathbb Q^d$, are there integers $n_1, \ldots, n_k$ with $A_1^{n_1} \cdots A_k^{n_k} x = y$? The source proves this undecidable in an appendix, from the generalized matrix powering problem, which it reduces from Hilbert's tenth problem. The LTI system has dimension $(k+1)d + k$ and block diagonal transition matrix $\mathrm{diag}(I_d, A_1, \ldots, A_k, I_k)$; its set of controls is $V_1 + \cdots + V_k$, where an atomic control in $V_i$ subtracts a vector $z$ from the $i$-th block of the state, adds it to the $(i+1)$-st block and adds $1$ to the $i$-th of the last $k$ coordinates, and this sum is a finite union of affine subspaces. From $s = (x, 0, \ldots, 0)$ the target $t = (0, \ldots, 0, y, 1, \ldots, 1)$ forces each atomic control to be used exactly once, at times $t_1, \ldots, t_k$, and the block $A_i$ is applied $t_{i+1} - t_i$ times between them; so $t$ is reachable iff suitable integer exponents exist (every integer tuple arises as differences of nonnegative times). A good expansion links a page for the undecidability of vector reachability for invertible rational matrices with integer exponents (Theorem A.3 of the source, via the generalized matrix powering problem of Theorem A.1).

The same paper shows that for control sets $V \cup \{0\}$ with $V$ an affine subspace, and for convex polytopes, the problem is at least as hard as Skolem's problem and the positivity problem for linear recurrence sequences, respectively, and that it is decidable for convex polytopes under spectral assumptions on $A$.

## Sources

- Nathanaël Fijalkow, Joël Ouaknine, Amaury Pouly, João Sousa-Pinto and James Worrell, "On the decidability of reachability in linear time-invariant systems", in *Proceedings of the 22nd ACM International Conference on Hybrid Systems: Computation and Control (HSCC 2019)*, ACM, 2019, pp. 77–86, <https://doi.org/10.1145/3302504.3311796>; read as arXiv:1802.06575v2, <https://arxiv.org/abs/1802.06575v2>: Theorem 2.1 in Section 2.1 ("Undecidability") of that version, its proof with Claims 2.2 and 2.3, and Appendix A ("Undecidability for invertible matrix problems": Theorem A.1 on generalized matrix powering and Theorem A.3 on vector reachability); the polynomial-time case for linear control sets is recalled in Section 1 of that version, after R. Kannan and R. J. Lipton.
