# Uniformity of a random linear combination over a finite field

Let $F$ be a finite field, $I$ a finite index set and $d \in F^I$ with $d_{i_0} \ne 0$ for some $i_0$. If $r \in F^I$ is uniformly random, then $\sum_{i \in I} r_i d_i$ is uniformly distributed on $F$; in particular it equals any fixed $t \in F$, and in particular $0$, with probability exactly $1/|F|$.

## Proof sketch

The map $r \mapsto \sum_i r_i d_i$ is an additive homomorphism $F^I \to F$, surjective because $r_{i_0}$ can be chosen to hit any value. All fibers of a surjective group homomorphism are cosets of the kernel, hence have equal size $|F|^{|I|-1}$.

## Sources

- R. Motwani and P. Raghavan, "Randomized Algorithms", Cambridge University Press, 1995.
- O. Goldreich, "Computational Complexity: A Conceptual Perspective", Cambridge University Press, 2008.
