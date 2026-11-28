# Deep learning fundamentals

What does a network compute, how is it trained, and what can be done with its learned features? These paths use three different mathematical objects: a map from inputs to outputs, a loss on examples, and an inference rule for new inputs.

## Layers and approximation

Begin with [a feedforward network](../supervised-learning/backpropagation/net.md) and [its forward pass](../supervised-learning/backpropagation/forward.md). ReLU networks illustrate the difference between [interpolating finitely many observations](../supervised-learning/finite-sample-expressivity-of-relu-networks/exists-relu-net-eq.md) and [approximating a continuous function uniformly on a compact set](../../../Analysis/approximation-theory/universal-approximation.md). Neither says which weights training will find. Other ways to organize layers include [residual networks](../supervised-learning/residual-networks-as-discretised-flows/residual-network-flow-error-le.md) and [message-passing graph neural networks](../supervised-learning/message-passing-gnns-and-1-wl-color-refinement.md).

- [Coordinatewise activation](coordinatewise-activation.md)
- [Multilayer perceptron (MLP)](multilayer-perceptron.md)
- [Multichannel convolutional layer](multichannel-convolutional-layer.md)

## State, memory and sequence models

A recurrent cell updates a fixed-size state; a memory network instead reads a collection of slots. For parallel sequence processing continue to [Transformer encoder and decoder blocks](../transformers-and-language-models/transformer-encoder-and-decoder-blocks.md), [encoder-only, causal and prefix masks](../transformers-and-language-models/transformer-visibility-patterns.md), and [why causal decoding can reuse cached keys and values](../transformers-and-language-models/cached-decoding-prefix-equivalence.md).

- [Recurrent neural network (RNN)](recurrent-neural-network.md)
- [Long short-term memory (LSTM) cell](long-short-term-memory-cell.md)
- [Gated recurrent unit (GRU)](gated-recurrent-unit.md)
- [Sequence encoder and autoregressive decoder](sequence-encoder-and-decoder.md)
- [A read hop in an end-to-end memory network](end-to-end-memory-network.md)

## Learning from gradients

[Backpropagation](../supervised-learning/backpropagation/backward-eq.md) computes a derivative; an optimizer chooses how to use it. Compare a scalar learning-rate schedule with Adam's per-coordinate scaling and the [matrix-aware Muon update](../supervised-learning/matrix-aware-optimizers/muon.md).

- [Minibatch SGD with momentum](minibatch-sgd-with-momentum.md)
- [Adam with bias-corrected moments](adam-optimizer.md)
- [AdamW: decoupled weight decay](adamw-decoupled-weight-decay.md)
- [Warmup and inverse-square-root learning-rate decay](warmup-and-inverse-square-root-decay.md)

## Reconstruction, generation and representation learning

The targets distinguish these objectives: reconstruct the input, model its likelihood, discriminate real samples from generated ones, or recognize another view of the same example.

- [Autoencoder reconstruction objective](autoencoder-reconstruction.md)
- [Diagonal-Gaussian variational autoencoder](diagonal-gaussian-variational-autoencoder.md)
- [Generative adversarial network (GAN) objective](generative-adversarial-objective.md)
- [Optimal discriminator for a fixed generator](optimal-gan-discriminator.md)
- [The GAN value is minimized by distribution matching](gan-value-and-distribution-matching.md)
- [Contrastive learning with paired views (NT-Xent)](contrastive-loss-for-paired-views.md)

## Retrieval in a learned embedding

Compare the exact answer to an index's returned set. [Locality-sensitive hashing](../../randomized-algorithms/approximate-near-neighbor-search/lsh-index.md) addresses a [radius-based near-neighbor problem](../../randomized-algorithms/approximate-near-neighbor-search/approximate-near-neighbor-problem.md); that guarantee is not a recall score for an approximate top-k query.

- [Exact top-k neighbors in embedding space](top-k-neighbors-in-embedding-space.md)
- [Weighted k-nearest-neighbor classification](weighted-knn-classification.md)
- [Recall at k for approximate neighbor search](recall-at-k-for-approximate-search.md)
- [Approximate neighbor search by product quantization](product-quantized-neighbor-search.md)
- [Querying a hierarchical navigable small-world index](hnsw-neighbor-retrieval.md)
- [Nearest-neighbor language model](nearest-neighbor-language-model.md)
