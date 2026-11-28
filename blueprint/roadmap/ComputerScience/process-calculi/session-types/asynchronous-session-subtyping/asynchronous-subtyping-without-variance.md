# Asynchronous session subtyping without covariance and contravariance is undecidable

Asynchronous session subtyping remains undecidable when outputs of the subtype must be matched by outputs with exactly the same labels and inputs likewise, so that only output anticipation distinguishes it from type equality.

Let $\le$ now denote the asynchronous subtyping of Bravetti, Carbone and Zavattaro (Theoretical Computer Science 722, 2018, Definition 2.4): the relation of [asynchronous subtyping](asynchronous-subtyping-of-binary-session-types.md) with one more condition in clause 2, namely that if $\mathcal{A} \ne [\,]^1$ then every continuation $T_i$ ($i \in I$) contains at least one input branching (no orphan messages). The relation $\le_{\mathsf{tout}}$ adds the requirement $I = J_k$ in clause 2 (no output covariance), $\le_{\mathsf{tin}}$ adds $I = J$ in clause 3 (no input contravariance), and $\le_{\mathsf{tin,tout}}$ adds both. As in the source, session types here are closed (every recursion variable lies under a binder $\mu \mathbf{t}$) with guarded recursion (in $\mu \mathbf{t}.T$, the variable $\mathbf{t}$ occurs only under an output or input), and an instance is a pair of such finite type terms over a finite set of labels.

**Theorem.** Each of the relations $\le_{\mathsf{tin,tout}}$, $\le_{\mathsf{tin}}$ and $\le_{\mathsf{tout}}$ on session types is undecidable: no algorithm decides, given $T$ and $S$, whether $T$ is related to $S$.

## Depends on

- [Asynchronous subtyping of binary session types](asynchronous-subtyping-of-binary-session-types.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

None.

## Expansion

The proof encodes single consuming queue machines, in which every dequeue is immediately followed by a state that only enqueues; their termination problem remains undecidable (Theorem 4.8 of the source). For such a machine $M$ and input $x$, a variant encoding gives types with $[\![s]\!]^{\emptyset} \le_{\mathsf{tin,tout}} [\![x\#]\!]$ exactly when $M$ does not terminate on $x$ (Theorem 4.11). On these types covariance and contravariance are never used, so the same equivalence holds for $\le_{\mathsf{tin}}$, $\le_{\mathsf{tout}}$ and $\le$ (Corollaries 4.12 and 4.13). The relation $\le_{\mathsf{tin,tout}}$ is closed under duality; by contrast, the source proves decidability for single-output types without input contravariance and for single-input types without output covariance. A good expansion links a page for the undecidability of termination for single consuming queue machines (Theorem 4.8 of the source), the problem the reduction starts from.

## Sources

- Mario Bravetti, Marco Carbone and Gianluigi Zavattaro, "On the boundary between decidability and undecidability of asynchronous session subtyping", *Theoretical Computer Science* 722, 19–51, 2018, <https://doi.org/10.1016/j.tcs.2018.02.010>; read as arXiv:1703.00659v3, <https://arxiv.org/abs/1703.00659v3>: Definitions 2.4 and 2.8 (restrictions $\mathsf{tin}$ and $\mathsf{tout}$), Definition 4.7, Theorems 4.8 and 4.11, Corollaries 4.12 and 4.13 of that version.
