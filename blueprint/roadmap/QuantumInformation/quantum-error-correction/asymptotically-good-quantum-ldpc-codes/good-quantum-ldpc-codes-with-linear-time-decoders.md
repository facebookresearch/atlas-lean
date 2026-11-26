# Dinur-Hsieh-Lin-Vidick: good quantum LDPC codes with linear-time decoders

For every $r \in (0, 1/2)$ there are $\delta > 0$, $w \in \mathbb{N}$ and an explicit infinite family of quantum LDPC codes with stabilizer weight at most $w$, rate $r$ and relative distance $\delta$, equipped with a linear-time decoder that corrects errors up to a linear distance. The codes are the CSS codes of the three-term chain complex

$$
\mathbb{F}_2^{F} \xrightarrow{\ \partial_2\ } (\mathbb{F}_2^{m_a})^{E^-} \oplus (\mathbb{F}_2^{m_b})^{E^|} \xrightarrow{\ \partial_1\ } (\mathbb{F}_2^{m_a \times m_b})^{V}
$$

on the squares, horizontal and vertical edges and vertices of a four-fold left-right Cayley complex $G^2(G, A, B)$ with $|A| = |B| = \Delta$, built from Tanner codes with local parity-check maps $H_A : \mathbb{F}_2^{\Delta} \to \mathbb{F}_2^{m_a}$ and $H_B : \mathbb{F}_2^{\Delta} \to \mathbb{F}_2^{m_b}$ of a suitable pair of local codes $C_A, C_B$. Positive rate needs two different local dimensions: the rate is at least $-(2\rho_a - 1)(2\rho_b - 1)/(2(2 - \rho_a - \rho_b))$ for $\rho_a = \dim C_A/\Delta$ and $\rho_b = \dim C_B/\Delta$, which is positive only when $\rho_a$ and $\rho_b$ lie on opposite sides of $1/2$, so $m_a \ne m_b$; the simplified one-$m$ description with $m_a = m_b$ has zero rate.

## Proof sketch

The local codes are taken so that $C_A, C_B, C_A^\perp, C_B^\perp$ have linear distance and both $(C_A, C_B)$ and $(C_A^\perp, C_B^\perp)$ are $\Theta(\Delta)$-robust (equivalently product-expanding), which random codes of the chosen rates achieve. Combined with spectral expansion of the Cayley graphs, robustness gives small-set boundary and coboundary expansion of locally minimal chains, hence linear distance in both directions. Decoding is split by direction. In the co-chain direction a small-set-flip decoder, which repeatedly flips a local pattern that reduces the syndrome weight, is a linear-time co-decoder. For the chain direction the decoder is not the same greedy procedure: it runs the co-decoder of the complex built with the dual local codes $(C_A^\perp, C_B^\perp)$ and then reconstructs the error from its output, which gives a linear-time decoder for the other error type.

## Depends on

- [Left-right Cayley complexes](../../../InformationTheory/error-correcting-codes/left-right-cayley-complex-codes/left-right-cayley-complex.md)

## Proof depends on

- [Random pairs of codes and their duals are product-expanding](random-pairs-of-codes-are-product-expanding.md)
- [Leverrier-Zemor: quantum Tanner codes are asymptotically good](quantum-tanner-codes-have-linear-distance.md)

## Sources

- Irit Dinur, Min-Hsiu Hsieh, Ting-Chun Lin, Thomas Vidick, "Good quantum LDPC codes with linear time decoders", STOC (2023); arXiv:2206.07750, Theorem 1.1, Section 3.1 (equation (6)), Lemma 3.3 and Theorems 4.1-4.2; footnote 2 notes that the one-$m$ simplification has zero rate.
