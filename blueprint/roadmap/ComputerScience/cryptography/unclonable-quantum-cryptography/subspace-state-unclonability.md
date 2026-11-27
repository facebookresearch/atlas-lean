# Query lower bound for duplicating subspace states

Let $A\subseteq\mathbb{F}_2^{n}$ be a uniformly random subspace of dimension $n/2$ and $|A\rangle=|A|^{-1/2}\sum_{a\in A}|a\rangle$. Given one copy of $|A\rangle$ and quantum oracle access to membership oracles for $A$ and for its dual $A^{\perp}$, every algorithm that outputs a state on two registers both of which pass the projective test onto $|A\rangle$ (implemented with the two membership oracles via $\Pi_A$ and the Hadamard-conjugated $\Pi_{A^\perp}$) with probability at least $\epsilon$, where $1/\epsilon=o(2^{n/2})$, must make $\Omega(\sqrt{\epsilon}\cdot 2^{n/4})$ queries.

## Proof sketch

The projector onto $|A\rangle$ equals $\Pi_A\cdot H^{\otimes n}\Pi_{A^{\perp}}H^{\otimes n}$, so the oracles suffice for verification. The lower bound uses an inner-product (hybrid/adversary) argument showing that, with few queries, the algorithm's output is nearly independent of which subspace among a large family containing $A$ was chosen, while cloning would require distinguishing them; a complementary-slackness style argument relates success to the adversary weight.

## Proof depends on

- [Public-key quantum money and quantum lightning](public-key-quantum-money.md)
- [Polynomial method for quantum query complexity](../../quantum-algorithms/quantum-query-lower-bounds/polynomial-method-for-quantum-query-complexity.md)
- [No-cloning theorem (linear form)](../../../QuantumInformation/quantum-operations/no-cloning-linear.md)

## Sources

- Scott Aaronson, Paul Christiano, "Quantum Money from Hidden Subspaces", STOC (2012), arXiv:1203.4740.
