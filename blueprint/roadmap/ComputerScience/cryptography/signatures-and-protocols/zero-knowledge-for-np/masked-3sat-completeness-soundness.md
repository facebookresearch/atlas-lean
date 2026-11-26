# Completeness and soundness of the masked 3SAT protocol

In the three-copy masked 3SAT protocol: (i) if $w$ satisfies $f(a)$, the honest prover makes the verifier accept with probability $1$; (ii) if $f(a)$ is unsatisfiable and $3m + 1 \le \ell(m)$ for all $m$, then no prover, even computationally unbounded and stateful, makes the verifier accept with probability greater than $1 - 1/(3|\varphi|)$, where $|\varphi|$ is the number of clauses (statistical binding of the PRG commitments holds except with probability $2^{-m}$). Sequentially repeating the protocol $k$ times multiplies the soundness bound: if no stateful prover makes one execution accept with probability more than $c$, then no prover makes all $k$ sequential executions accept with probability more than $c^k$.

## Proof sketch

Statistical binding fixes the committed values. If the formula is unsatisfiable, some clause or consistency relation fails in the committed data, and the verifier picks it with probability at least $1/(3|\varphi|)$. Sequential repetition: condition on the history and bound each round's acceptance by $c$.

## Depends on

- [The three-copy masked 3SAT zero-knowledge protocol](masked-3sat-zero-knowledge-protocol.md)

## Sources

- Oded Goldreich, Silvio Micali and Avi Wigderson, "Proofs that Yield Nothing but Their Validity or All Languages in NP Have Zero-Knowledge Proof Systems", Journal of the ACM, 1991.
- Oded Goldreich, "Foundations of Cryptography, Volume 2: Basic Applications", Cambridge University Press, 2004.
