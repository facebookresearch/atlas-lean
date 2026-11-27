# Yao's protocol over a garbling scheme in the oblivious-transfer hybrid model

Let $\mathcal{G}$ be a projective garbling scheme with side information $\Phi$ that is prv.sim secure. In Yao's protocol in the batched-OT hybrid model, the garbler garbles the circuit $f$, sends the garbled circuit, the labels of its own input bits and the decoding information, and offers the label pairs of the evaluator's input wires to the ideal batched OT; the evaluator obtains the labels of its input, evaluates and decodes (in the two-sided version it returns the output to the garbler). Then: (i) both parties output $f(x_0, x_1)$ in every run; (ii) the protocol is perfectly private against a corrupted garbler; (iii) against a corrupted evaluator, the semi-honest advantage equals the prv.sim advantage of an explicit reduction against the garbling scheme with the evaluator's simulator built from the garbling simulator, and the simulator is polynomial time when the garbling simulator is. Instantiating $\mathcal{G}$ with point-and-permute (from a PRF), Free-XOR (from a circular $2$-correlation robust hash) or half-gates (from a CCR hash) gives semi-honest secure two-party computation in the OT-hybrid model.

## Proof sketch

The garbler's view contains only its own coins and the output. The evaluator's view is the garbling triple on the joint input plus OT answers, which are exactly the encoded input labels; the simulator runs the garbling simulator on the output and $\Phi(f)$.

## Depends on

- [Correctness and privacy of Free-XOR garbling under circular correlation robustness](../boolean-garbling-constructions/free-xor-security.md)
- [Side-information functions and privacy notions for garbling schemes](../garbling-scheme-security/garbling-privacy-notions.md)
- [Ideal 1-out-of-2, batched and 1-out-of-4 oblivious transfer](../oblivious-transfer-protocols/oblivious-transfer-functionalities.md)
- [Security of Yao's garbled-circuit protocol against semi-honest adversaries](../security-of-yao-s-garbled-circuit-protocol.md)

## Proof depends on

- [Point-and-permute garbling is correct and simulation private from a PRF](../boolean-garbling-constructions/point-and-permute-security.md)
- [Correctness and privacy of half-gates garbling](../boolean-garbling-constructions/half-gates-security.md)
- [Correctness and privacy of Free-XOR garbling under circular correlation robustness](../boolean-garbling-constructions/free-xor-security.md)

## Sources

- Andrew Chi-Chih Yao, "How to Generate and Exchange Secrets", Proceedings of the 27th Annual Symposium on Foundations of Computer Science, 1986.
- Yehuda Lindell and Benny Pinkas, "A Proof of Security of Yao's Protocol for Two-Party Computation", Journal of Cryptology, 2009.
- Mihir Bellare, Viet Tung Hoang and Phillip Rogaway, "Foundations of Garbled Circuits", Proceedings of the 2012 ACM Conference on Computer and Communications Security, 2012.
