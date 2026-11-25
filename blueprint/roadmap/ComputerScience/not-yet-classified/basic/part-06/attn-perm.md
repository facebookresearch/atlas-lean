# Self-attention is permutation-equivariant

For token embeddings $X_1, \dots, X_n$, weight matrices $W_Q$, $W_K$ (key dimension $d_k \ge 1$) and $W_V$, and any permutation $\sigma$ of the tokens, softmax self-attention without positional encoding or mask satisfies $\mathrm{attn}(X_{\sigma(\cdot)})_i = \mathrm{attn}(X)_{\sigma(i)}$ for every token $i$.
