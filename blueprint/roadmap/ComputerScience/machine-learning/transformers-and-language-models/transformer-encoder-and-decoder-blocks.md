# Original Transformer encoder and decoder blocks

Start with token embeddings scaled by $\sqrt{d_{\rm model}}$ plus position encodings. The original model shares the weight matrix of its two token embeddings with the pre-softmax vocabulary readout. The original **post-normalization** architecture wraps each sublayer $F$ by $R_F(X)=\operatorname{LN}(X+F(X))$, with its own normalization parameters. Residuals have the same width as their inputs. Write $P(x)=W_2\operatorname{ReLU}(W_1x+b_1)+b_2$ for the same feedforward map at each position (column-vector notation).

An encoder block applies, in order, a wrapped all-to-all self-attention sublayer and a wrapped $P$. A decoder block applies three wrapped sublayers: causal self-attention (row $i$ sees $j\le i$), cross-attention (queries from that decoder stream, keys and values from the final encoder states), and $P$. Stacking blocks means composing them, not tying their weights. A linear vocabulary readout followed by softmax predicts the next target token from shifted target inputs. These are inference equations with dropout disabled.

## Depends on

- [Masked multi-head attention](masked-multi-head-attention.md)
- [Tokenwise layer normalization](tokenwise-layer-normalization.md)
- [Multilayer perceptron (MLP)](../deep-learning-foundations/multilayer-perceptron.md)
- [Sequence encoder and autoregressive decoder](../deep-learning-foundations/sequence-encoder-and-decoder.md)

## Sources

- Vaswani et al., [*Attention Is All You Need*](https://arxiv.org/abs/1706.03762) (NeurIPS 2017), §§3.1–3.5 and figure 1.
