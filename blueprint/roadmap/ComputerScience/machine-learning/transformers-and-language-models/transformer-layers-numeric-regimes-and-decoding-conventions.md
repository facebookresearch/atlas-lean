# Transformer layers, numeric regimes and decoding conventions

This node covers transformer layers built from attention, together with the numeric regimes, attention variants and
output conventions that expressivity results fix; softmax single-head attention itself is defined separately.

## Expansion

A sound expansion has separate pages for:

1. **Layers.** A layer composes multi-head self-attention, residual connections and a position-wise feedforward
   map; a transformer composes layers over token embeddings plus positional encodings.
2. **Numeric regime.** Exact rationals or reals, fixed precision, or $O(\log n)$-bit precision, stated for each
   result that uses the model.
3. **Attention variants.** Softmax, hard (argmax) and averaging-hard attention, each with its tie convention.
4. **Output convention.** Single-pass recognition or autoregressive decoding with a stated number of steps.

## Sources

- J. Pérez, P. Barceló and J. Marinković, *Attention is Turing complete*, JMLR 22 (2021): the transformer with hard attention, rational arithmetic and autoregressive decoding (Section 3). <https://jmlr.csail.mit.edu/papers/volume22/20-302/20-302.pdf>
- W. Merrill and A. Sabharwal, *The parallelism tradeoff: limitations of log-precision transformers*, TACL 2023: the $c\log n$-precision model and single-pass recognition. <https://arxiv.org/abs/2207.00729>
