# Autoencoder reconstruction objective

An encoder $E_\phi:\mathbb R^d\to\mathbb R^m$ produces a code; a decoder $D_\theta:\mathbb R^m\to\mathbb R^d$ maps it back to the input space. For a nonempty dataset and squared error the training objective is

$$\frac1N\sum_{i=1}^N\|x_i-D_\theta(E_\phi(x_i))\|_2^2.$$

The target is the input itself, not a separate label or translated sequence. An undercomplete autoencoder has $m<d$; this restricts the code dimension but does not by itself rule out memorization of a finite dataset. An unconstrained identity map can have zero reconstruction error without learning a useful representation.

## Depends on

- [Empirical risk](../generalization-bounds-and-concentration/empirical-risk.md)

## Background

- [Sequence encoder and autoregressive decoder](sequence-encoder-and-decoder.md)

## Sources

- Goodfellow, Bengio and Courville, *Deep Learning* (MIT Press, 2016), [chapter 14, Autoencoders](https://www.deeplearningbook.org/contents/autoencoders.html).
