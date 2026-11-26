# Dekker's error-free product without a fused multiply-add

Work in binary floating-point arithmetic with $p$-bit significands, $p \ge 6$, an unbounded exponent range and [rounding to nearest with ties to even](fl.md), writing $\mathrm{fl}$ for the rounded result of an operation. Let $a$ and $b$ be [floating-point numbers](is-float.md), and let $(a_{\mathrm{hi}}, a_{\mathrm{lo}})$ and $(b_{\mathrm{hi}}, b_{\mathrm{lo}})$ be their [Veltkamp splittings](veltkamp-splitting.md) with splitting point $\lceil p/2 \rceil$. The algorithm

$$\begin{aligned} x &= \mathrm{fl}(ab), & e_1 &= \mathrm{fl}\bigl(x - \mathrm{fl}(a_{\mathrm{hi}} b_{\mathrm{hi}})\bigr), & e_2 &= \mathrm{fl}\bigl(e_1 - \mathrm{fl}(a_{\mathrm{lo}} b_{\mathrm{hi}})\bigr), \\ e_3 &= \mathrm{fl}\bigl(e_2 - \mathrm{fl}(a_{\mathrm{hi}} b_{\mathrm{lo}})\bigr), & y &= \mathrm{fl}\bigl(\mathrm{fl}(a_{\mathrm{lo}} b_{\mathrm{lo}}) - e_3\bigr) & & \end{aligned}$$

returns floating-point numbers $x$ and $y$ with

$$ab = x + y$$

exactly, where $x = \mathrm{fl}(ab)$ and $y = ab - \mathrm{fl}(ab)$ is its rounding error, and $x$ and $y$ are nonoverlapping and moreover nonadjacent, in the sense of the [Veltkamp splitting](veltkamp-splitting.md) page (zero overlaps no number; for $a = b = 1$, $(x, y) = (1, 0)$). (With any other rule for breaking ties between the two nearest floating-point numbers, the identity and nonoverlap still hold; nonadjacency uses ties to even.) Every product and subtraction after the first is exact; the algorithm uses only additions and multiplications, in contrast with the [error-free product via a fused multiply-add](error-free-transformation-of-a-product-via-fused-multiply-ad.md), which computes $y = \mathrm{fl}(ab - x)$ in one operation.

## Depends on

- [Binary floating-point numbers](is-float.md)
- [Round to nearest, ties to even](fl.md)
- [Veltkamp splitting of a floating-point number](veltkamp-splitting.md)

## Proof depends on

- [Sterbenz's lemma](is-float-sub.md)
- [The relative error bound](abs-fl-sub-le.md)
- [Ties to even for floating-point rounding](even-of-abs-fl-sub-eq.md)

## Related topics

- [Error-free transformation of a product via fused multiply-add](error-free-transformation-of-a-product-via-fused-multiply-ad.md)

## Sources

- J. R. Shewchuk, "Adaptive precision floating-point arithmetic and fast robust geometric predicates", *Discrete & Computational Geometry* 18(3):305–363, 1997; technical report version CMU-CS-96-140R, Section 2.5, Theorem 18 with the algorithm TWO-PRODUCT, Figure 12 and the proof, which credits the method to G. W. Veltkamp through Dekker. <https://people.eecs.berkeley.edu/~jrs/papers/robustr.pdf>
