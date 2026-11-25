# Distinguishing advantage between encryptions

The distinguishing advantage of a distinguisher $D$ between encryptions of the messages $m$ and $m'$
is $\lvert \Pr[D \text{ outputs } 1 \text{ on } m] - \Pr[D \text{ outputs } 1 \text{ on } m'] \rvert$,
the two probabilities being those of the [indistinguishability experiment](ind-exp.md) for $m$ and
for $m'$.

## Sources

- O. Goldreich, *Foundations of Cryptography, Vol. II: Basic Applications*, Cambridge University Press, 2004, Section 5.2, Definition 5.2.4.
