# Fingerprinting code

A fingerprinting code for $n$ users of length $d$ with keys in `Key`
is a pair of randomized algorithms: a generator, which draws a codebook $C$ together with a key,
and a tracing algorithm, which maps a key and a word to an accused user $i \in [n]$ or to $\bot$,
no accusation. The key is the state that the generator shares with tracing; tracing receives no
other input from the generator, so a key may hold the codebook itself.

## Sources

- M. Bun, J. Ullman and S. Vadhan, *Fingerprinting codes and the price of approximate differential privacy*, SIAM J. Comput. 47(5), 2018, arXiv:1311.3158v3, Section 3.1.
- S. Vadhan, *The complexity of differential privacy*, in *Tutorials on the Foundations of Cryptography*, Springer, 2017, Definition 5.16 in the author's version of 9 August 2016.
