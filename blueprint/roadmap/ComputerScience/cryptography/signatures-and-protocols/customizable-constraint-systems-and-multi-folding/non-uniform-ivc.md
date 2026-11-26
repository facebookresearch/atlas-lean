# Non-uniform incrementally verifiable computation

Let $F_1,\dots,F_k$ be polynomial-time step functions on a common state space and $\phi$ a polynomial-time selector. A *non-uniform IVC (NIVC)* scheme proves statements of the form: there exist $w_0,\dots,w_{n-1}$ such that $z_{i+1}=F_{\phi(z_i,w_i)}(z_i,w_i)$ for all $i< n$. Completeness, knowledge soundness and succinctness are as for IVC, with the additional efficiency requirement that the prover's work at step $i$ is proportional to $|F_{\phi(z_i,w_i)}|$ rather than to $\sum_j|F_j|$ (no universal circuit). NIVC models the execution of a machine with an instruction set, where $F_j$ implements instruction $j$.

## Depends on

- [Incrementally verifiable computation scheme for an iterated function](../incrementally-verifiable-computation-and-pcd/ivc-scheme.md)

## Sources

- Abhiram Kothapalli, Srinath Setty, "SuperNova: Proving Universal Machine Executions without Universal Circuits", IACR ePrint 2022/1758 (2022).
