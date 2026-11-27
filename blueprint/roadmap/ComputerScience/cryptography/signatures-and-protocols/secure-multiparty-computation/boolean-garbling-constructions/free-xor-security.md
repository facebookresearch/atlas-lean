# Correctness and privacy of Free-XOR garbling under circular correlation robustness

Free-XOR garbling is correct for every hash, tweak assignment, offset and base labels, provided the free gates compute XOR. If labels have characteristic two, distinct table slots use distinct tweaks, and $H$ is circular correlation robust, then Free-XOR garbling is prv.sim secure with side information $\Phi_{\mathrm{xor}}$ (topology plus the set of XOR gates): there is one universal simulator such that every probabilistic polynomial-time adversary has negligible advantage, and per instance the advantage is at most the CCR advantage of an explicit reduction.

## Proof sketch

Every inactive label equals an active label plus $\Delta$, so each inactive table row is a hash value $H(x \oplus \Delta, t)$ at a fresh tweak; replacing the CCR oracle by a random function makes those rows uniform, and the remaining view is simulated from $\Phi_{\mathrm{xor}}$ and the output.

## Depends on

- [Free-XOR garbling](free-xor-garbling.md)
- [Side-information functions and privacy notions for garbling schemes](../garbling-scheme-security/garbling-privacy-notions.md)
- [Circular correlation robust hash functions](../garbling-scheme-security/circular-correlation-robustness.md)

## Proof depends on

- [Indistinguishability versus simulation privacy of garbling schemes](../garbling-scheme-security/garbling-ind-versus-sim.md)

## Sources

- Vladimir Kolesnikov and Thomas Schneider, "Improved Garbled Circuit: Free XOR Gates and Applications", Automata, Languages and Programming, 35th International Colloquium, 2008.
- Seung Geol Choi, Jonathan Katz, Ranjit Kumaresan and Hong-Sheng Zhou, "On the Security of the ``Free-XOR'' Technique", Theory of Cryptography, 2012.
- Samee Zahur, Mike Rosulek and David Evans, "Two Halves Make a Whole: Reducing Data Transfer in Garbled Circuits Using Half Gates", Advances in Cryptology – EUROCRYPT 2015, 2015.
