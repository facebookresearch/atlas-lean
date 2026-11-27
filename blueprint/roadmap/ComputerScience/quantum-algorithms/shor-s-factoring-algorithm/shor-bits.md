# Bit string of a computational-basis measurement outcome

Let $M \in \mathbb{N}$ and $y \in \{0, 1, \dots, 2^M - 1\}$. The bit string of the measurement outcome $y$ is its $M$-bit binary expansion, least significant bit first: the list $(b_0, b_1, \dots, b_{M-1})$ of bits with

$$y = \sum_{i=0}^{M-1} b_i\, 2^i.$$

It is the string that classical post-processing reads from the computational-basis outcome $y$ of an $M$-qubit measurement. Nothing about it is specific to Shor's algorithm: it is the measured bit string of any $M$-qubit outcome.
