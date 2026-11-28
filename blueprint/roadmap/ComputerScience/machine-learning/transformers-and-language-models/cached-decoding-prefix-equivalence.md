# Cached decoding agrees with full-prefix evaluation

Fix a causal Transformer, its weights and a token sequence. Assume deterministic inference in exact arithmetic, position encodings and visibility masks that do not change old rows when the prefix grows, tokenwise normalization and feedforward maps, and an unmodified cache with no eviction. Then incremental evaluation gives the same next-token logits as recomputing each entire prefix from scratch.

Induct on prefix length, starting with empty caches. To extend a prefix by one token, work through the layers from bottom to top. Earlier input embeddings have not changed. If the earlier inputs to a layer agree, so do their projected keys and values. Causality leaves every earlier attention row unchanged; the new query sees exactly the old cached entries plus the new key and value, just as in the last row of the full-prefix pass. The tokenwise operations preserve equality. At the top layer the logits match and all caches are correct for the extended prefix.

This is not a claim of bitwise equality for different floating-point kernels, or of equivalence for a bidirectional encoder.

## Depends on

- [Causal key–value cache](causal-key-value-cache.md)
- [Original Transformer encoder and decoder blocks](transformer-encoder-and-decoder-blocks.md)
- [Encoder-only, causal and prefix Transformer masks](transformer-visibility-patterns.md)

## Proof depends on

- [Masked multi-head attention](masked-multi-head-attention.md)

## Sources

- Derived from the parallel and incremental attention equations in Shazeer, [*Fast Transformer Decoding: One Write-Head is All You Need*](https://arxiv.org/abs/1911.02150) (2019), §§2.3–2.4, and the tokenwise sublayers in Vaswani et al., [*Attention Is All You Need*](https://arxiv.org/abs/1706.03762) (NeurIPS 2017), §3.
