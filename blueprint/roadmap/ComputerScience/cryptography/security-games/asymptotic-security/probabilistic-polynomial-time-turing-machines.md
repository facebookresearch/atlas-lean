# Probabilistic polynomial-time Turing machines

A *probabilistic* (randomized) Turing machine is a Turing machine with an additional read-only random tape whose cells hold independent, uniformly distributed bits. On an input $x$ its output is therefore a random variable over the choice of the random tape. It runs in time $T(n)$ if for every input $x \in \{0, 1\}^*$ and every content of the random tape it halts within $T(|x|)$ steps, and it is a *probabilistic polynomial-time* (PPT) machine if it runs in time $q(n)$ for some polynomial $q$, so that the bound also covers short inputs, including the empty one. A PPT machine is *uniform*: one machine serves every input length, as opposed to a non-uniform family of machines, one for each input length.

## Depends on

- [Runs of a machine given by a transition function](../../../../TheoryOfComputation/turing-machines/multi-tape-and-multi-stack/multi-tape-turing-machines/run-from-of-tr.md)

## Sources

- R. Pass and A. shelat, *A Course in Cryptography*, lecture notes, Cornell University, 2010, <https://www.cs.cornell.edu/courses/cs4830/2010fa/lecnotes.pdf>, Definitions 23.4 and 23.5, and Definition 26.8 for the non-uniform contrast
