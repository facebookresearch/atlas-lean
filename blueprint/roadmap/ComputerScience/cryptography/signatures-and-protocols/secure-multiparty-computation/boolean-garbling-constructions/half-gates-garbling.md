# Half-gates garbling

*Half-gates* garbling of circuits over XOR and AND gates uses Free-XOR labels $W, W \oplus \Delta$ with colour bits. An AND gate $c = a \wedge b$ is split into two half gates, each with a single ciphertext: with $p_a, p_b$ the colours of the zero-labels $W_a, W_b$ and tweaks $j, j'$,

$$
T_G = H(W_a, j) \oplus H(W_a \oplus \Delta, j) \oplus p_b\Delta, \qquad T_E = H(W_b, j') \oplus H(W_b \oplus \Delta, j') \oplus W_a,
$$

and $W_c = H(W_a, j) \oplus p_a T_G \oplus H(W_b, j') \oplus p_b (T_E \oplus W_a)$. The evaluator holding labels $A = W_a \oplus v_a\Delta$ and $B = W_b \oplus v_b\Delta$ with colours $s_a, s_b$ computes $H(A, j) \oplus s_a T_G \oplus H(B, j') \oplus s_b(T_E \oplus A)$. Each AND gate costs exactly two ciphertexts and XOR gates are free.

## Depends on

- [Free-XOR garbling](free-xor-garbling.md)

## Sources

- Samee Zahur, Mike Rosulek and David Evans, "Two Halves Make a Whole: Reducing Data Transfer in Garbled Circuits Using Half Gates", Advances in Cryptology – EUROCRYPT 2015, 2015.
