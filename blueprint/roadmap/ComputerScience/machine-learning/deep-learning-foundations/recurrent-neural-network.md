# Recurrent neural network (RNN)

Given $h_0\in\mathbb R^m$ and inputs $x_1,\ldots,x_T\in\mathbb R^d$, a recurrent network iterates the **same** transition $h_t=F_\theta(x_t,h_{t-1})$. In the vanilla affine-plus-activation cell,

$$h_t=\sigma^{[m]}(W_xx_t+W_hh_{t-1}+b),\qquad y_t=W_yh_t+c.$$

Here $W_x$ is $m\times d$, $W_h$ is $m\times m$, and the readout maps the hidden state to the desired output dimension. Unrolling produces an acyclic computation for each finite $T$, but not $T$ independent parameter sets. The final state depends only on the prefix consumed; the empty input returns $h_0$.

## Depends on

- [Coordinatewise activation](coordinatewise-activation.md)

## Background

- [The forward pass](../supervised-learning/backpropagation/forward.md)

## Sources

- Goodfellow, Bengio and Courville, *Deep Learning* (MIT Press, 2016), [chapter 10, Sequence Modeling](https://www.deeplearningbook.org/contents/rnn.html).
- Cho et al., [*Learning Phrase Representations using RNN Encoder–Decoder for Statistical Machine Translation*](https://aclanthology.org/D14-1179/) (EMNLP 2014), §2.1.
