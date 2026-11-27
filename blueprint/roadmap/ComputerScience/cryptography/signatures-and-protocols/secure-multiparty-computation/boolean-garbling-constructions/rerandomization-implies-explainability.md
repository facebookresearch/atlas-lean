# Rerandomization privacy implies explainable garbling

For a rerandomizable garbling scheme: (i) for every distinguisher, the advantage in the explainable-garbling game (telling an honestly garbled circuit with its coins from a rerandomized circuit with explanation coins) equals its advantage in the rerandomization-privacy game; (ii) if the action of label permutations on encodings respects composition of permutations, then the explainable-rerandomization advantage is at most the rerandomization-privacy advantage of an explicit distinguisher. Hence rerandomization privacy gives both explainability notions, as needed for malicious-security compilers that let parties prove their garbled material was honestly generated.

## Proof sketch

Both games are the same experiment after renaming the coins; for (ii), composing two rerandomizations is a rerandomization by the composed permutation.

## Depends on

- [Rerandomizable and explainable garbling schemes](rerandomizable-garbling.md)

## Sources

- Anasuya Acharya, Carmit Hazay, Vladimir Kolesnikov and Manoj Prabhakaran, "Malicious Security for SCALES: Outsourced Computation with Ephemeral Servers", Advances in Cryptology – CRYPTO 2024, 2024.
