# Generation from independent biases

The generator that draws the $d$ column biases
independently from $\mu$, then a codebook with these biases, and returns the codebook with the
bias vector as the key: Tardos's construction for a discrete bias distribution $\mu$ on $[0, 1]$.
Tardos draws each bias as $\sin^2 r$ for $r$ uniform on an interval, a continuous distribution,
which a probability mass function cannot express.

## Sources

- G. Tardos, *Optimal probabilistic fingerprint codes*, J. ACM 55(2), 2008, Section 2.1.
