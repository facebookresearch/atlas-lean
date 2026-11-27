# Removing code words does not increase the error

Let $C = (x_1, \dots, x_K)$ be a code and $e : \{1, \dots, M\} \to \{1, \dots, K\}$ injective, and let
$C \circ e = (x_{e(1)}, \dots, x_{e(M)})$ be the subcode it keeps. Under maximum-likelihood decoding
with ties counted as errors, every kept word has at most its error probability in $C$:

$$P_{e,m}(C \circ e) \le P_{e,e(m)}(C).$$

A competitor $m' \ne m$ in the subcode is the competitor $e(m') \ne e(m)$ in $C$.

## Background

- [Error probability of maximum-likelihood decoding](ml-error-prob.md)

## Sources

- R. G. Gallager, "A simple derivation of the coding theorem and some applications", IEEE Trans. Inform. Theory IT-11(1):3–18, January 1965, proof of Corollary 2.
