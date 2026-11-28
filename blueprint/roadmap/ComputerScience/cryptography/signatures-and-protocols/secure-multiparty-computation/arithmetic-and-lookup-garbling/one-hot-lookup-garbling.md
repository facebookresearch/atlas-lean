# One-hot garbling of lookup tables

For a lookup table $T : \iota \to \{0,1\}^\kappa$ viewed as a truth-table matrix, (i) *one-hot selection*: $T^{\mathsf T}\, e_x = T(x)$ for the one-hot vector $e_x$; in characteristic two the product of $T$ with the Free-XOR offsets of a bit vector $v$ is the offset of $T v$, so if the evaluator holds Free-XOR labels of $e_x$ it can compute labels of every output bit $T(x)_u$ locally. (ii) The *binary-to-one-hot* gadget (one-hot garbling) converts Free-XOR labels of the bits of $x \in \{0,1\}^n$, for an evaluator who knows $x$ in the clear, into labels of the one-hot vector $e_x \in \{0,1\}^{2^n}$ with $n - 1$ garbled ciphertexts ($(n-1)\lambda$ bits for security parameter $\lambda$, in Heath's formulation); it is correct for every hash and offset, and if the hash is circular correlation robust (distinct tweaks per doubling step), the evaluator's view, one label per bit together with the ciphertexts, is indistinguishable from a view simulated from $x$, exactly so when the hash is a random function. The evaluator learns $x$, so (i) and (ii) give privacy-free lookup tables with a number of ciphertexts logarithmic in the table size. Private lookup tables, for an evaluator who does not know $x$, need further masking: the logrow scheme of Heath, Kolesnikov and Ng garbles a table with $N$ rows and $m$ output bits, $n = \lceil \log_2 N \rceil$, with $(n-1)\lambda + nm\lambda + Nm$ bits.

## Proof sketch

(i) is matrix multiplication by a standard basis vector and linearity of the offset map. (ii) The labels of one bit already form a one-hot vector of length $2$; each of the remaining $n - 1$ doubling steps splits every one-hot label by the next input bit using one ciphertext, which needs the evaluator to know that bit; under a random function each ciphertext is masked by an unqueried hash value.

## Depends on

- [Free-XOR garbling](../boolean-garbling-constructions/free-xor-garbling.md)
- [Circular correlation robust hash functions](../garbling-scheme-security/circular-correlation-robustness.md)

## Sources

- David Heath, Vladimir Kolesnikov and Lucien K. L. Ng, "Garbled Circuit Lookup Tables with Logarithmic Number of Ciphertexts", Advances in Cryptology – EUROCRYPT 2024, 2024.
- David Heath, "Efficient Arithmetic in Garbled Circuits", Advances in Cryptology – EUROCRYPT 2024, 2024.
