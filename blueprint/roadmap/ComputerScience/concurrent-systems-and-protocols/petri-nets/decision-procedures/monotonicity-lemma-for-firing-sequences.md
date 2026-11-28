# Monotonicity lemma for Petri net firing sequences

Let $N$ be an ordinary [Petri net](../place-transition-petri-nets.md) and let $M$ and $L$ be markings of $N$, added placewise.

1. If $M [\sigma\rangle M'$ for a finite sequence of transitions $\sigma$, then $M + L [\sigma\rangle M' + L$.
2. If an infinite sequence $\sigma = t_1 t_2 \cdots$ is enabled at $M$, that is, $M [t_1\rangle M_1 [t_2\rangle M_2 \cdots$ for some markings $M_1, M_2, \dots$, then $\sigma$ is enabled at $M + L$.

## Depends on

- [Place/transition Petri nets](../place-transition-petri-nets.md)

## Sources

- J. Esparza, *Petri Nets*, lecture notes, Technical University of Munich, version of 18 June 2019, <https://archive.model.in.tum.de/um/courses/petri/SS2019/PNSkript.pdf>, Definitions 1.3.2 and 1.3.4, Proposition 1.3.6 and Lemma 1.3.7 ("Monotonicity lemma"), pp. 15–16.
