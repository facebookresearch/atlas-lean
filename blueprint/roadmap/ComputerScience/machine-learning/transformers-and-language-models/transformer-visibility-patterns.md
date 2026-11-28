# Encoder-only, causal and prefix Transformer masks

Number valid input positions $1,\dots,n$ and ignore padding. A single Transformer stack can use any of the following self-attention visibility sets, at **every** layer:

- Bidirectional encoder (as in BERT): $S_i=\{1,\dots,n\}$; a masked-token prediction sees the *corrupted* sequence, which may contain a mask, a random replacement, or an unchanged selected token.
- Causal decoder-only language model: $S_i=\{1,\dots,i\}$. The readout at $i$ predicts token $i+1$, not the observed input at $i$.
- Prefix language model, with prefix length $0\le p\le n$: $S_i=\{1,\dots,p\}$ for $i\le p$, and $S_i=\{1,\dots,i\}$ for $i>p$. Source-prefix positions can see each other but cannot see target tokens.

An encoder–decoder uses two stacks and a separate cross-attention sublayer rather than simply changing the mask in one stack. These are information-flow patterns, not assertions that the models learn the same functions.

## Depends on

- [Masked multi-head attention](masked-multi-head-attention.md)
- [Original Transformer encoder and decoder blocks](transformer-encoder-and-decoder-blocks.md)

## Background

- [Transformer expressivity: Turing completeness vs log-precision TC0 upper bound](transformer-expressivity-turing-completeness-vs-log-precisio.md)

## Sources

- Devlin et al., [*BERT*](https://aclanthology.org/N19-1423/) (NAACL 2019), §3.
- Raffel et al., [*Exploring the Limits of Transfer Learning with a Unified Text-to-Text Transformer*](https://jmlr.org/papers/v21/20-074.html) (JMLR 2020), §3.2.1 and figures 3–4.
