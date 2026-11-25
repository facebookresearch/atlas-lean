# Lower semicontinuity of the total cost

Let $Z$ be a Polish space and $c : Z \to [0, \infty]$ continuous. The map $\pi \mapsto \int c \, d\pi$
is lower semicontinuous on Borel probability measures on $Z$ with the topology of weak convergence.

Proof: $\int c \, d\pi = \sup_n \int \min(c, n) \, d\pi$ by monotone convergence; each truncated
functional is lower semicontinuous by the portmanteau theorem (the liminf of the measures of an open
set is at least its limit measure); a supremum of lower semicontinuous functions is lower
semicontinuous. Villani writes a lower semicontinuous cost as an increasing limit of continuous
functions in the same way.

## Sources

- C. Villani, *Optimal Transport: Old and New*, Grundlehren der mathematischen Wissenschaften 338, Springer 2009, Lemma 4.3 (nonnegative case).
