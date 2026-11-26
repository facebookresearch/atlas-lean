# Rerandomizable and explainable garbling schemes

A *rerandomizable garbling scheme* is a projective garbling scheme with an additional algorithm $\mathrm{ReRand}$ that maps a garbled circuit $F$ (with its encoding information) to a fresh-looking garbling $F'$ of the same function, together with an action of label permutations on encodings. *Rerandomization privacy* requires that $\mathrm{ReRand}(F)$ is distributed (computationally) as a fresh garbling of $f$, even given the original $F$. A scheme is *explainable* if, given a garbled circuit, one can efficiently produce coins explaining it as an honest garbling.

## Depends on

- [Side-information functions and privacy notions for garbling schemes](../garbling-scheme-security/garbling-privacy-notions.md)

## Sources

- Anasuya Acharya, Carmit Hazay, Vladimir Kolesnikov and Manoj Prabhakaran, "Malicious Security for SCALES: Outsourced Computation with Ephemeral Servers", Advances in Cryptology – CRYPTO 2024, 2024.
