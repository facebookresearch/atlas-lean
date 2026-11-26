# Non-uniform incrementally verifiable computation

Let $F_1,\dots,F_\ell$ ($\ell\ge 1$) be polynomial-time functions, each taking a state of $s$ field elements and a non-deterministic input to a new state, and let $\varphi$ be a polynomial-time *control function* mapping a state and a non-deterministic input to an index in $\{1,\dots,\ell\}$; all are given as arithmetic circuits. A *non-uniform IVC (NIVC)* scheme consists of a generator $\mathsf{G}(1^{\lambda},N)\to\mathsf{pp}$, a deterministic encoder $\mathsf{K}(\mathsf{pp},((F_1,\dots,F_\ell),\varphi))\to(\mathsf{pk},\mathsf{vk})$, a prover and a verifier. The statement $(i,z_0,z)$ claims knowledge of $\omega_0,\dots,\omega_{i-1}$ such that the iteration $z_{j+1}=F_{\varphi(z_j,\omega_j)}(z_j,\omega_j)$ for $j<i$ ends at $z_i=z$. Given $\mathsf{pk}$, a statement $(i,z_0,z_i)$, advice $\omega_i$ and a proof $\Pi_i$, the prover outputs a proof $\Pi_{i+1}$ for $(i+1,z_0,F_{\varphi(z_i,\omega_i)}(z_i,\omega_i))$, and the verifier decides a statement from $\mathsf{vk}$ and a proof. The scheme must satisfy:

- *Completeness:* if $\Pi_i$ is accepted for $(i,z_0,z_i)$, then the updated proof is accepted for the updated statement, with probability $1$.
- *Knowledge soundness:* for every constant $n$ and every expected polynomial-time adversary outputting functions, $(z_0,z)$ and a proof accepted for $(n,z_0,z)$, an expected polynomial-time extractor given the same random tape outputs $\omega_0,\dots,\omega_{n-1}$ whose iteration from $z_0$ ends at $z$, with probability negligibly close to the adversary's acceptance probability.
- *Succinctness:* the proof size is independent of the iteration count.
- *Efficiency:* the prover's time at step $i$ is linear in the size of the function applied at step $i$ and in the number $\ell$ of functions, rather than in $|F_1|+\dots+|F_\ell|$.

For $\ell=1$ this is ordinary IVC. NIVC models a machine with an instruction set, where $F_j$ implements instruction $j$ and $\varphi$ computes the next instruction.

## Depends on

- [Incrementally verifiable computation scheme for an iterated function](../incrementally-verifiable-computation-and-pcd/ivc-scheme.md)

## Sources

- Abhiram Kothapalli, Srinath Setty, "HyperNova: Recursive Arguments for Customizable Constraint Systems", CRYPTO (2024), IACR ePrint 2023/573, Section 3, Definition 7.
