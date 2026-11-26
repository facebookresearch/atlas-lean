# Correctness and privacy of half-gates garbling

(i) *Half-gates identity:* the evaluator's computation on labels $W_a \oplus v_a\Delta$, $W_b \oplus v_b\Delta$ returns $W_c \oplus (v_a v_b)\Delta$; hence half-gates garbling is correct for every hash, tweaks, offset and input labels, and the garbled table has exactly $2$ ciphertexts per AND gate. (ii) If $H$ is circular correlation robust and distinct half gates use distinct tweaks, half-gates garbling is prv.sim secure with side information $\Phi_{\mathrm{circ}}$: one universal simulator works for every probabilistic polynomial-time adversary, with advantage at most the CCR advantage of an explicit reduction per instance.

## Proof sketch

(i) Expand both half gates by cases on the colours, using $s_a = p_a \oplus v_a$. (ii) Each ciphertext contains exactly one hash value at an inactive label $x \oplus \Delta$ under a fresh tweak; under CCR the table is uniform for every choice of input labels, and the evaluator's view is simulated from the circuit and output.

## Depends on

- [Half-gates garbling](half-gates-garbling.md)
- [Side-information functions and privacy notions for garbling schemes](../garbling-scheme-security/garbling-privacy-notions.md)
- [Circular correlation robust hash functions](../garbling-scheme-security/circular-correlation-robustness.md)

## Proof depends on

- [Indistinguishability versus simulation privacy of garbling schemes](../garbling-scheme-security/garbling-ind-versus-sim.md)

## Sources

- Samee Zahur, Mike Rosulek and David Evans, "Two Halves Make a Whole: Reducing Data Transfer in Garbled Circuits Using Half Gates", Advances in Cryptology – EUROCRYPT 2015, 2015.
