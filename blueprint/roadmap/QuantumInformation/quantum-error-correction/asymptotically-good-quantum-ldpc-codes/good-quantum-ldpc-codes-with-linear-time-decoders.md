# Dinur-Hsieh-Lin-Vidick: good quantum LDPC codes with linear-time decoders

There is an explicit family of asymptotically good quantum LDPC codes, defined from a three-term chain complex $(\mathbb{F}_2^{m \times m})^{V} \to (\mathbb{F}_2^{m})^{E} \to \mathbb{F}_2^{F}$ on the vertices, edges and squares of a left-right Cayley complex with a pair of constant-size random codes, together with a decoder running in linear time that corrects a constant fraction of adversarial errors.

## Proof sketch

The main ingredient is an essentially optimal robustness property for the tensor product of two random codes, equivalent to product-expansion of the pair and of the dual pair. Robustness implies that the chain complex is a small-set coboundary and boundary expander, which gives both linear distance and the correctness of a greedy decoder that flips local codewords reducing the syndrome.

## Depends on

- [Random pairs of codes and their duals are product-expanding](random-pairs-of-codes-are-product-expanding.md)
- [Left-right Cayley complexes](../../../InformationTheory/error-correcting-codes/left-right-cayley-complex-codes/left-right-cayley-complex.md)
- [Leverrier-Zemor: quantum Tanner codes are asymptotically good](quantum-tanner-codes-have-linear-distance.md)

## Proof depends on

- [Random pairs of codes and their duals are product-expanding](random-pairs-of-codes-are-product-expanding.md)
- [Left-right Cayley complexes](../../../InformationTheory/error-correcting-codes/left-right-cayley-complex-codes/left-right-cayley-complex.md)
- [Leverrier-Zemor: quantum Tanner codes are asymptotically good](quantum-tanner-codes-have-linear-distance.md)

## Sources

- Irit Dinur, Min-Hsiu Hsieh, Ting-Chun Lin, Thomas Vidick, "Good quantum LDPC codes with linear time decoders", STOC (2023); arXiv:2206.07750.
