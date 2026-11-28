# Sequence encoder and autoregressive decoder

For a source sequence $x_{1:n}$, an encoder computes a representation $c=E(x_{1:n})$. Given $c$ and a start symbol, a decoder produces normalized distributions over a finite target vocabulary. The conditional probability of a particular target sequence **including its end symbol** is

$$p(y_{1:m}\mid x_{1:n})=\prod_{t=1}^m p_D(y_t\mid y_{<t},c).$$

The input and target need not be the same length, language, or even alphabet. In the recurrent encoder–decoder $c$ can be the final recurrent state; in an attention-based decoder it can be a whole sequence of encoder states. This defines probabilities of terminated strings without assuming that every decoder terminates almost surely.

## Background

- [Recurrent neural network (RNN)](recurrent-neural-network.md)

## Sources

- Cho et al., [*Learning Phrase Representations using RNN Encoder–Decoder for Statistical Machine Translation*](https://aclanthology.org/D14-1179/) (EMNLP 2014), §2.2.
- Vaswani et al., [*Attention Is All You Need*](https://arxiv.org/abs/1706.03762) (NeurIPS 2017), §3.
