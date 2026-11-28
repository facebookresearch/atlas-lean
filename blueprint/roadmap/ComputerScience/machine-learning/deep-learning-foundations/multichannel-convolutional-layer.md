# Multichannel convolutional layer

Let $x_{j,c}$ be an input on a length-$n$ grid with $C$ channels. For a filter of width $1\le k\le n$, $F$ output channels, unit stride and no padding, a convolutional neural network layer computes

$$y_{i,f}=\sigma\!\left(b_f+\sum_{s=0}^{k-1}\sum_{c=1}^{C}W_{s,c,f}\,x_{i+s,c}\right),\qquad 0\le i\le n-k,\quad 1\le f\le F.$$

The same $kCF$ kernel coefficients serve every position: locality restricts the inputs to one window, and sharing ties the weights across windows. This is the deep-learning cross-correlation convention (no kernel reversal). The range of $i$ is part of the definition: no invariance at an artificial boundary is assumed.

## Depends on

- [Coordinatewise activation](coordinatewise-activation.md)

## Sources

- Goodfellow, Bengio and Courville, *Deep Learning* (MIT Press, 2016), [chapter 9, §§9.1–9.2 (weight sharing) and §9.5, equations (9.7)–(9.8) (multichannel filters and stride)](https://www.deeplearningbook.org/contents/convnets.html).
- Hardt and Recht, *Patterns, Predictions, and Actions* (2022), [Deep learning, “Deep models and feature representation”](https://mlstory.org/deep.html).
