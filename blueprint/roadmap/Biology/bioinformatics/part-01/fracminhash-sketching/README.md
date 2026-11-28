# FracMinHash sketching

A FracMinHash sketch keeps every element of a $k$-mer set whose hash falls below a fixed fraction $s$ of the hash range, so the sketch size scales with the set size. The resulting containment estimator has a bias that depends only on $s$ and the set size, is asymptotically normal, and, under a simple point-mutation model, yields a point estimate and a confidence interval for the mutation rate between two sequences.

- [Bias correction, variance and asymptotic normality of the FracMinHash containment estimator](fracminhash-containment-estimator.md)
- [Mutation-rate confidence interval from FracMinHash containment](mutation-rate-confidence-interval-from-fracminhash-containment.md)
