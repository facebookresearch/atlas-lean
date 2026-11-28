# Causal key–value cache

In left-to-right decoding, store the projected keys and values of past positions **separately for each layer and KV head**. The empty prefix starts with empty arrays. At position $t$, compute the new query, key and value from the current input to that layer and append $(k_t,v_t)$. Attend with $q_t$ to the populated arrays $(k_1,\dots,k_t)$ and $(v_1,\dots,v_t)$, including the current entry. Past queries are not cached.

For $L$ layers, $B$ sequences of equal length $T$, $G$ KV heads per layer, and key/value widths $d_k,d_v$, the live entries require $LB T G(d_k+d_v)$ scalars. This counts neither padding, allocation metadata, nor precision in bytes. The cache avoids recomputing old projections; full-context attention still reads a growing prefix.

## Depends on

- [Masked multi-head attention](masked-multi-head-attention.md)
- [Grouped-query and multi-query attention](grouped-query-attention.md)
- [Encoder-only, causal and prefix Transformer masks](transformer-visibility-patterns.md)

## Background

- [Multi-head latent attention (MLA)](../attention-and-low-rank-adaptation/multi-head-latent-attention.md)

## Sources

- Shazeer, [*Fast Transformer Decoding: One Write-Head is All You Need*](https://arxiv.org/abs/1911.02150) (2019), §§2.4 and 3, incremental attention pseudocode.
