# Transformers and language models

Transformer encoder and decoder models with explicit numeric regimes, their expressivity, and the calibration-based lower bound on hallucination for generative language models.

Start with [one scaled dot-product attention head](../../not-yet-classified/basic/part-06/attn.md). Multiple heads can read a source sequence, a causal prefix, or a bidirectional input. For prerequisites on networks and training, see [Deep learning fundamentals](../deep-learning-foundations/README.md).

- [Masked multi-head attention](masked-multi-head-attention.md)
- [Tokenwise layer normalization](tokenwise-layer-normalization.md)
- [Original Transformer encoder and decoder blocks](transformer-encoder-and-decoder-blocks.md)
- [Encoder-only, causal and prefix Transformer masks](transformer-visibility-patterns.md)
- [Grouped-query and multi-query attention](grouped-query-attention.md)
- [Causal key–value cache](causal-key-value-cache.md)
- [Cached decoding agrees with full-prefix evaluation](cached-decoding-prefix-equivalence.md)

Compare [rotary position embeddings](../attention-and-low-rank-adaptation/rotary-position-embedding.md), [delta-rule linear attention](../attention-and-low-rank-adaptation/delta-rule-linear-attention.md) and [multi-head latent attention](../attention-and-low-rank-adaptation/multi-head-latent-attention.md). For expressivity, the numeric regime and output convention matter as well:

- [Calibration of predictors and the calibrated-LM hallucination lower bound](calibration-of-predictors-and-the-calibrated-lm-hallucinatio.md)
- [Transformer expressivity: Turing completeness vs log-precision TC0 upper bound](transformer-expressivity-turing-completeness-vs-log-precisio.md)
- [Transformer layers, numeric regimes and decoding conventions](transformer-layers-numeric-regimes-and-decoding-conventions.md)
