# Polynomial neural networks for homomorphic inference

A *polynomial network* in the sense of CryptoNets is a feed-forward network whose layers are weighted sums with public integer weights and biases, the square activation $z\mapsto z^2$, and scaled mean pooling (window sums without division). It computes a vector of integer polynomials in its input, of degree at most $2^L$ for $L$ square layers.

Inputs and weights are fixed-precision reals scaled to integers. The layers are:

- *weighted sum* $z\mapsto Wz+b$ (convolution or fully connected) with integer $W$ and $b$ known in the clear to the evaluator;
- *square activation*, $z_j\mapsto z_j^2$ coordinatewise, in place of sigmoid or rectified linear activations;
- *scaled mean pooling*, $z\mapsto\sum_{j\in S}z_j$ over each pooling window $S$, in place of max pooling.

Consecutive layers with no square activation between them may be collapsed into one weighted sum. Every output coordinate is a polynomial with integer coefficients in the input, of degree at most $2^L$, and the square layers are the only layers that multiply two input-dependent values. CryptoNets evaluates such networks under homomorphic encryption, with the weights as plaintexts; the source recommends taking these replacements into account during training.

## Depends on

None.

## Proof depends on

None.

## Expansion

The degree bound is induction on layers: weighted sums and pooling preserve degree, squaring doubles it. Exact encrypted evaluation (plaintext range, noise, CRT over several plaintext moduli, slot batching) is a separate result.

## Sources

- Ran Gilad-Bachrach, Nathan Dowlin, Kim Laine, Kristin Lauter, Michael Naehrig, John Wernsing, "CryptoNets: Applying Neural Networks to Encrypted Data with High Throughput and Accuracy", ICML 2016, PMLR 48, §2 and §§3.2.1–3.2.5, [PMLR copy](https://proceedings.mlr.press/v48/gilad-bachrach16.html).
- Pengtao Xie, Misha Bilenko, Tom Finley, Ran Gilad-Bachrach, Kristin Lauter, Michael Naehrig, "Crypto-Nets: Neural Networks over Encrypted Data", arXiv:1412.6181 (2014), the earlier approach that replaces activations by approximating polynomials.
