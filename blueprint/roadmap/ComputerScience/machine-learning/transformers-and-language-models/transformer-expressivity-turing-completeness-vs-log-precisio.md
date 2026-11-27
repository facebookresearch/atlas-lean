# Transformer expressivity: Turing completeness vs log-precision TC0 upper bound

This node collects expressivity results for transformers, each for its own model.

## Expansion

A sound expansion has separate pages for:

1. **Turing completeness** (Pérez, Barceló and Marinković, Theorem 6): transformers with positional encodings,
   arbitrary-precision rational arithmetic, hard attention and unbounded autoregressive decoding are Turing
   complete.
2. **Circuit upper bound** (Merrill and Sabharwal): transformers whose arithmetic uses $O(\log n)$ bits of
   precision on inputs of length $n$, with feedforward networks computable in linear space, recognize only
   languages in logspace-uniform $\mathsf{TC}^0$ in a single pass (a depth-$d$ transformer is simulated by logspace-uniform
   threshold circuits of depth $3 + (9 + 2d_\oplus)d$); consequences such as the inability to solve
   certain problems are conditional on unproved separations (for example $\mathsf{L} \ne \mathsf{P}$).
3. The two results concern different models (precision, attention and decoding) and do not conflict; no
   unconditional separation is claimed.

A good expansion adds a page for each pending prerequisite below and links it under the dependency sections.

- Statement prerequisite: Transformer encoder/decoder model with precision regimes.
- Statement prerequisite: Turing machine.

## Sources

- Attention is Turing Complete (Perez, Barcelo, Marinkovic, JMLR 22, 2021), Theorem 6. <https://jmlr.csail.mit.edu/papers/volume22/20-302/20-302.pdf>
- The Parallelism Tradeoff: Limitations of Log-Precision Transformers (Merrill & Sabharwal, TACL 2023; arXiv:2207.00729) — arXiv / TACL: Theorem 2 (uniform simulation by threshold circuits). <https://arxiv.org/abs/2207.00729>
