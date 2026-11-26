# Watrous's oblivious quantum rewinding lemma for zero-knowledge simulation

Let $Q$ be a quantum circuit acting on an auxiliary input state $|\psi\rangle$ and fresh ancillas, outputting a qubit $b$ and a state, such that the probability $p(\psi)$ that $b=0$ is independent of $|\psi\rangle$ up to an error $\epsilon$, with $p\ge p_0>0$. Then there is a quantum circuit of size $O(\log(1/\delta)/(p_0(1-p_0)))\cdot|Q|$ that, on input $|\psi\rangle$, outputs a state within trace distance $O(\delta+\epsilon\log(1/\delta)/(p_0(1-p_0)))$ of the normalized post-selected state of $Q$ conditioned on $b=0$. Consequently, classical zero-knowledge proofs whose simulators succeed with input-independent probability (such as Graph Isomorphism or 3-coloring with perfectly hiding commitments) remain zero knowledge against quantum malicious verifiers.

## Proof sketch

When the success probability is input-independent, the circuit $Q$ restricted to the input space acts on a two-dimensional invariant subspace for each input in the same way, so amplitude amplification (alternating reflections about the success projector and the initial state) rotates towards the success subspace obliviously, without knowing or copying the input. Approximate independence adds a proportional error.

## Depends on

- [Zero-knowledge interactive proofs](../../signatures-and-protocols/zero-knowledge-and-arguments/zero-knowledge-interactive-proofs.md)
- [Trace distance: metric, operational form and contractivity](../../../../QuantumInformation/quantum-states-distances-and-entropy/remaining-clauses-of-trace-distance-and-contractivity.md)

## Sources

- John Watrous, "Zero-Knowledge against Quantum Attacks", SIAM Journal on Computing (2009); STOC (2006).
