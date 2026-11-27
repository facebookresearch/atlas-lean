# Probability-one complete factoring with a fixed finite quantum gate set

There is one circuit family indexed by input length $\ell$, generated from the unary word $1^\ell$ by one deterministic polynomial-time finite-stack machine with finite alphabets. The same polynomial bounds both qubits and gate count for all $\ell$. The explicit description gives the width, instruction count and each gate's primitive name, inverse and control bits, and ordered wire list, using unary self-delimiting naturals. Gates act on distinct wires. The primitive matrices are NOT, CNOT, Toffoli, Hadamard and $\mathrm{diag}(1,i)$. Each can be used in its original or conjugate-transpose form, and with or without one added control wire as first wire (identity on control zero). There are twenty gate names, each of arity at most four.

For every integer $N\ge2$ of bit length $\ell$, put $n=\max(128,\ell)$. There are at least $\ell+n^2$ wires. The first $\ell$ contain $N$ in little-endian order and all other wires start in the zero basis state. Apply the gates in list order and read the next $n^2$ wires as $n$ little-endian $n$-bit integers. The sum of squared complex norms over all output basis strings whose decoded list is the nondecreasing prime factorization of $N$, with multiplicities and padded by zeros, is exactly $1$. Other output wires are unconstrained. This is exact Born success, not a bounded-error family or postselection.

## Depends on

- The fixed circuit instruction set, finite-alphabet length generator and exact Born readout above.

## Proof depends on

- A probability-one factorization construction, an exact implementation in the listed finite gate set, resource bounds at every length, and a length-only generator producing those concrete instructions.

## Expansion

Prove matrix semantics, unitarity and padding/readout correctness in a native circuit model. Isolate exact factor recovery and the uniform resource certificates. Approximate Fourier transforms and success amplification alone do not imply exact probability one.

## Sources

- OpenAI, [ExactQuantumFactoring.lean, gates, encoding, probability and `MainTheorem`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/ExactQuantumFactoring.lean#L11-L150).
