# Indistinguishability implies semantic security, per adversary

Let $A$ be an adversary, $X$ a plaintext distribution, $h$ and $f$ functions on plaintexts and
$\varepsilon \ge 0$. Suppose that for every plaintext $x$ in the support of $X$ the
[distinguisher hardwiring $x$](ss-distinguisher.md) has
[advantage](ind-advantage.md) at most $\varepsilon$ between encryptions of $x$ and of the dummy message
of length $|x|$. Then the probability that $A$ wins the [real experiment](ss-real.md) is at most
$\varepsilon$ more than the probability that the [simulator](simulator.md) wins the
[ideal experiment](ss-ideal.md).

This is the concrete content of Goldreich's Proposition 5.2.6 and Claim 5.2.6.1: averaging over $x$
replaces his choice of a plaintext maximizing the gap. Only the distinguishers built from $A$, $h$ and
$f$ are needed, each with one call to $A$, so the statement carries over to efficient adversaries.

## Informally uses

- [Averaging a pointwise bound](../games-and-advantages/win-prob-bind-le.md): the per-plaintext bounds
  are averaged over $X$.

## Sources

- O. Goldreich, *Foundations of Cryptography, Vol. II: Basic Applications*, Cambridge University Press, 2004, Section 5.2, Proposition 5.2.6 and Claim 5.2.6.1.
