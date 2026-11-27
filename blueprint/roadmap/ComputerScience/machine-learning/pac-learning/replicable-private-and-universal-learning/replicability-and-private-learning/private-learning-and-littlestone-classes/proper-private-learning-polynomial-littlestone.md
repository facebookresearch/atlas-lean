# Proper private learning of Littlestone classes with polynomial sample complexity

Every class of Littlestone dimension $d$ is properly PAC learnable under approximate differential privacy with sample complexity $\tilde O(d^6)$, ignoring the polynomial dependence on the privacy and accuracy parameters. Moreover, the sample complexity of privately sanitizing (releasing accurate answers to all counting queries in) a binary class is polynomial in its Littlestone dimension and dual Littlestone dimension, so a class is privately sanitizable if and only if it has finite Littlestone dimension.

## Proof sketch

A class is **irreducible** if every restriction by a single labelled example that is consistent with many sample points does not lower its Littlestone dimension. Greedily restricting the class by examples that lower the Littlestone dimension yields, after at most $d$ steps, an irreducible subclass; for irreducible classes, the SOA output on a sample is globally stable with probability polynomial in $1/d$, and private selection over the at most $d$ reduction steps (sparse vector technique) keeps the learner proper. Sanitization follows from private learning of the dual class.

## Depends on

- [Private PAC learners and their sample complexity](private-pac-learner.md)
- [The Littlestone dimension is the optimal mistake bound](../../../../online-learning-and-boosting/the-littlestone-dimension-is-the-optimal-mistake-bound.md)

## Proof depends on

- [Finite Littlestone dimension implies private learnability](littlestone-classes-are-privately-learnable.md)
- [The exponential mechanism is differentially private](../../../../../cryptography/laplace-and-exponential-mechanisms/exp-mechanism-differentially-private.md)

## Sources

- B. Ghazi, N. Golowich, R. Kumar, P. Manurangsi, "Sample-efficient Proper PAC Learning with Approximate Differential Privacy", STOC (2021), arXiv:2012.03893.
