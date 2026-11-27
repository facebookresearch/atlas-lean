# Yao's protocol over DDH-based oblivious transfer

Replace the ideal batched OT in Yao's protocol by sequential masked transfers over the three-message DDH oblivious transfer with a key-derivation mask. Then, for every environment, the semi-honest advantage against the composed protocol is at most the advantage against the OT-hybrid protocol plus, for each of the evaluator's input wires, the advantage of a key-derivation or DDH distinguisher against the corresponding single transfer. Consequently, under DDH for the group family, pseudorandomness of the key derivation and prv.sim security of the garbling scheme, Yao's protocol is semi-honest secure in the plain model against a corrupted evaluator, and statistically secure against a corrupted garbler up to the exponent-sampling error.

## Proof sketch

Apply the composition bound round by round: each oblivious-transfer call of the outer protocol is replaced by the masked DDH transfer, whose simulator for the relevant corrupted party is supplied by the DDH-OT theorem and the masked-OT lemma.

## Depends on

- [Yao's protocol over a garbling scheme in the oblivious-transfer hybrid model](yao-protocol-ot-hybrid.md)

## Proof depends on

- [Three-message DDH oblivious transfer and the necessity of its consistency check](../oblivious-transfer-protocols/three-message-ddh-ot.md)
- [Oblivious transfer of masked values from oblivious transfer of pads](../oblivious-transfer-protocols/masked-ot-from-pad-ot.md)
- [Batched oblivious transfer from sequential single transfers](../oblivious-transfer-protocols/batch-ot-from-sequential-transfers.md)
- [Composition theorem for semi-honest multiparty protocols](../semi-honest-mpc-foundations/semi-honest-composition-theorem.md)

## Sources

- Yehuda Lindell and Benny Pinkas, "A Proof of Security of Yao's Protocol for Two-Party Computation", Journal of Cryptology, 2009.
- Andrew Chi-Chih Yao, "How to Generate and Exchange Secrets", Proceedings of the 27th Annual Symposium on Foundations of Computer Science, 1986.
- Dan Boneh and Victor Shoup, "A Graduate Course in Applied Cryptography", Version 0.6, 2023.
