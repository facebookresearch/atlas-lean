# Nearest-neighbor language model

From a fixed text collection, store $n\ge1$ pairs $(f(c_i),w_i)$: the key is a frozen language model’s encoding of a context and the value is its observed next token. For test context $c$ and $1\le k\le n$, retrieve the $k$ neighbor IDs $N_k$ by squared Euclidean distance $d_i=\|f(c)-f(c_i)\|_2^2$. The retrieved next-token distribution is

$$p_{\rm NN}(w\mid c)=\frac{\sum_{i\in N_k:\,w_i=w}\exp(-d_i)}{\sum_{i\in N_k}\exp(-d_i)}.$$

Several occurrences of the same token add probability mass; an absent token gets none from retrieval. The model uses $\lambda p_{\rm NN}+(1-\lambda)p_{\rm LM}$ for $0\le\lambda\le1$. An approximate index can supply the neighbors in practice, but may yield a different distribution. The datastore need not come from the model’s training corpus. It is distinct from an attention cache, which stores projections of the current sequence.

## Depends on

- [Exact top-k neighbors in embedding space](top-k-neighbors-in-embedding-space.md)
- [Softmax](../../not-yet-classified/basic/part-06/softmax.md)
- [Sequence encoder and autoregressive decoder](sequence-encoder-and-decoder.md)

## Background

- [Causal key–value cache](../transformers-and-language-models/causal-key-value-cache.md)

## Sources

- Khandelwal et al., [*Generalization through Memorization: Nearest Neighbor Language Models*](https://arxiv.org/abs/1911.00172) (ICLR 2020), §2, equations (1)–(3).
