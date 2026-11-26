# Watrous's oblivious quantum rewinding lemma for zero-knowledge simulation

Let $Q$ be a unitary quantum circuit on $n+k$ qubits. For an $n$-qubit state $|\psi\rangle$ write $Q|\psi\rangle|0^{k}\rangle=\sqrt{p(\psi)}\,|0\rangle|\phi_0(\psi)\rangle+\sqrt{1-p(\psi)}\,|1\rangle|\phi_1(\psi)\rangle$ with unit vectors $|\phi_0(\psi)\rangle,|\phi_1(\psi)\rangle$. Let $p_0,q\in(0,1)$ and $\epsilon\in(0,1/2)$ satisfy $|p(\psi)-q|<\epsilon$, $p_0(1-p_0)\le q(1-q)$ and $p_0\le p(\psi)$ for all $|\psi\rangle$. Then there is a general quantum circuit $R$ of size $O\bigl(\log(1/\epsilon)\,|Q|/(p_0(1-p_0))\bigr)$ whose output $\rho(\psi)$ on every input $|\psi\rangle$ satisfies

$$
\langle\phi_0(\psi)|\rho(\psi)|\phi_0(\psi)\rangle\ge 1-16\,\epsilon\,\frac{\log^{2}(1/\epsilon)}{p_0^{2}(1-p_0)^{2}}.
$$

Consequently, classical zero-knowledge proofs whose simulators succeed with input-independent probability, such as the Goldreich–Micali–Wigderson protocols for Graph Isomorphism and (assuming quantum computationally concealing, unconditionally binding commitments) for Graph 3-Colouring, remain zero knowledge against quantum malicious verifiers.

## Proof sketch

When the success probability is input-independent, the circuit $Q$ restricted to the input space acts on a two-dimensional invariant subspace for each input in the same way, so amplitude amplification (alternating reflections about the success projector and the initial state) rotates towards the success subspace obliviously, without knowing or copying the input. Approximate independence adds a proportional error.

## Depends on

- [Zero-knowledge interactive proofs](../../signatures-and-protocols/zero-knowledge-and-arguments/zero-knowledge-interactive-proofs.md)
- [Trace distance: metric, operational form and contractivity](../../../../QuantumInformation/quantum-states-distances-and-entropy/remaining-clauses-of-trace-distance-and-contractivity.md)

## Sources

- John Watrous, "Zero-Knowledge against Quantum Attacks", SIAM Journal on Computing (2009); STOC (2006).
