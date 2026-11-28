# Coordinatewise activation

A scalar activation $\sigma:\mathbb R\to\mathbb R$ acts on a feature vector $z\in\mathbb R^d$ by $[\sigma^{[d]}(z)]_j=\sigma(z_j)$. A dense hidden layer applies this map **after** forming $Wx+b$. ReLU uses $\max(0,t)$; a logistic gate uses $(1+e^{-t})^{-1}$. The former can output zero on a whole half-line; the latter takes values strictly between zero and one.

Why add a nonlinearity? With identity activations two successive affine layers give $W_2(W_1x+b_1)+b_2=(W_2W_1)x+(W_2b_1+b_2)$, still an affine map. Increasing depth alone cannot change that.

## Background

- [ReLU neuron](../supervised-learning/two-layer-neural-networks-and-barron-space/relu-neuron.md)

## Sources

- Goodfellow, Bengio and Courville, *Deep Learning* (MIT Press, 2016), [chapter 6, Deep Feedforward Networks](https://www.deeplearningbook.org/contents/mlp.html).
- Hardt and Recht, *Patterns, Predictions, and Actions* (2022), [Deep learning, “Deep models and feature representation”](https://mlstory.org/deep.html).
