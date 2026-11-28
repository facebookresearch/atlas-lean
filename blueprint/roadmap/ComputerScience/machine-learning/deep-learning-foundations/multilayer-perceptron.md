# Multilayer perceptron (MLP)

Fix positive widths $d_0,\ldots,d_L$ with $L\ge2$. A dense feedforward network with linear readout takes $h_0=x$ and computes

$$h_l=\sigma_l^{[d_l]}(W_lh_{l-1}+b_l)\quad(1\le l<L),\qquad f(x)=W_Lh_{L-1}+b_L.$$

Here $W_l\in\mathbb R^{d_l\times d_{l-1}}$, $b_l\in\mathbb R^{d_l}$, and each hidden activation is applied coordinatewise. The last layer has no activation in this convention; for classification its outputs can serve as logits. With one hidden layer and one output the nonlinear part is a weighted sum of ridge functions $\sigma(w_i^\top x+b_i)$. Approximation by such sums is an existence theorem, not a claim that training finds the weights.

## Depends on

- [Feedforward network](../supervised-learning/backpropagation/net.md)
- [The forward pass](../supervised-learning/backpropagation/forward.md)
- [Coordinatewise activation](coordinatewise-activation.md)

## Background

- [Universal approximation theorem](../../../Analysis/approximation-theory/universal-approximation.md)
- [Finite-sample expressivity of two-layer ReLU networks](../supervised-learning/finite-sample-expressivity-of-relu-networks/exists-relu-net-eq.md)
- [The backward pass is the vector-Jacobian product](../supervised-learning/backpropagation/backward-eq.md)

## Sources

- Goodfellow, Bengio and Courville, *Deep Learning* (MIT Press, 2016), [chapter 6, Deep Feedforward Networks](https://www.deeplearningbook.org/contents/mlp.html).
- Hardt and Recht, *Patterns, Predictions, and Actions* (2022), [Deep learning, “Deep models and feature representation”](https://mlstory.org/deep.html).
