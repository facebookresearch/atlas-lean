# The SiPhy rate matrix

For a finite state set $I$, a real $\omega$, a real matrix $R$ and real weights $\pi$, the SiPhy rate matrix is

$$Q_{ab} = \omega R_{ab} \pi_b \ (a \ne b), \qquad Q_{aa} = -\omega \sum_{k \ne a} R_{ak} \pi_k,$$

that is, $\omega$ times the [general time-reversible matrix](../time-reversible-nucleotide-substitution-models/gtr-rate.md) with exchangeabilities $R$ and frequencies $\pi$ (Garber et al. 2009, Eq. 10).

## Sources

- M. Garber, M. Guttman, M. Clamp, M. C. Zody, N. Friedman, X. Xie, *Identifying novel constrained elements by exploiting biased substitution patterns*, Bioinformatics 25 (2009), i54–i62, Eq. 10.
