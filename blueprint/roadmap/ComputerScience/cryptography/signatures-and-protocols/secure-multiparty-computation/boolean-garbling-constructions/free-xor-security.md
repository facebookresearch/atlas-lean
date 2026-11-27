# Correctness and privacy of Free-XOR garbling under circular correlation robustness

Free-XOR garbling is correct for every hash, gate indices, offset and base labels, provided the free gates compute XOR. Call $H$ *circular 2-correlation robust* if, for a uniform secret $R$, the oracle $(w, w', g, b_1, b_2, b_3) \mapsto H(w \oplus b_1 R \Vert w' \oplus b_2 R \Vert g) \oplus b_3 R$ is indistinguishable from a random function by every polynomial-time distinguisher making only legal queries: none with $(b_1, b_2) = (0, 0)$, and never both $(w, w', g, b_1, b_2, 0)$ and $(w, w', g, b_1, b_2, 1)$. If $H$ is circular 2-correlation robust, then Yao's two-party protocol in the OT-hybrid model with Free-XOR garbling (rows $H(A \Vert B \Vert g) \oplus C$) is secure against semi-honest adversaries. Its proof gives the garbling-level statement: for every circuit $f$ and input $x$, the evaluator's view (the garbled non-XOR gates, one label per input wire and the output decoding information) is simulated from the topology of $f$, its set of XOR gates and the output alone, and every distinguisher between the real and the simulated view yields a legal-query distinguisher against circular 2-correlation robustness with the same advantage. Hence Free-XOR garbling is prv.sim secure with side information $\Phi_{\mathrm{xor}}$ (topology plus the set of XOR gates), with one universal simulator, and per instance the advantage is at most the circular 2-correlation robustness advantage of an explicit reduction.

## Proof sketch

The simulator picks one random label and colour bit per wire not driven by an XOR gate, propagates them through XOR gates, makes the row each non-XOR gate's evaluator decrypts an honest encryption of the output label and the other three rows uniform, and sets the output decoding bit from the output. The reduction, which knows the actual wire values, writes every other row as an oracle answer at the active labels shifted by multiples of $R$; its queries are legal, the view is real when the oracle is real and simulated when it is a random function.

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
