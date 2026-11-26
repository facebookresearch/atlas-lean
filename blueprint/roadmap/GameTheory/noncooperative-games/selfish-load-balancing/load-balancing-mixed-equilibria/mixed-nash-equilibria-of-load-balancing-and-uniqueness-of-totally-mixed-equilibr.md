# Mixed Nash equilibria of load balancing and uniqueness of totally mixed equilibria

In a load-balancing game on related machines, the expected cost to job $i$ of machine $j$ under the mixed profile $p$ is $\mathbb{E}[\ell_j] + (1 - p_i(j))\, w_i / s_j$, and $p$ is a mixed Nash equilibrium iff every machine in the support of $p_i$ minimizes this quantity. If all weights are positive and the number of jobs is not $1$, there is at most one totally mixed Nash equilibrium. For two unit jobs on two machines of speeds $1$ and $s$, a totally mixed equilibrium exists iff $1/2 < s < 2$, and then each job chooses the speed-$1$ machine with probability $(2 - s)/(1 + s)$.

## Proof sketch

Job $i$'s own contribution to machine $j$ is $w_i/s_j$ exactly when it picks $j$, while others contribute in expectation. Indifference equations of a totally mixed equilibrium form a linear system in the probabilities whose matrix is invertible under the stated hypotheses.

## Depends on

- [Expected makespan of a mixed profile in load balancing](expected-makespan-of-a-mixed-profile-in-load-balancing.md)
- [Totally mixed Nash equilibrium](../../nash-s-theorem/universality-of-nash-equilibria/totally-mixed-nash-equilibrium.md)

## Proof depends on

- [Support characterization of mixed best responses](../../nash-s-theorem/support-characterization-of-mixed-best-responses.md)
- [Totally mixed Nash equilibria are the positive profiles with equal pure-strategy costs](../../nash-s-theorem/universality-of-nash-equilibria/totally-mixed-nash-equilibria-are-the-positive-profiles-with-equal-pure-strategy.md)

## Sources

- Elias Koutsoupias and Christos H. Papadimitriou, "Worst-Case Equilibria", STACS 99: 16th Annual Symposium on Theoretical Aspects of Computer Science, 1999.
- Marios Mavronicolas and Paul G. Spirakis, "The Price of Selfish Routing", Proceedings of the Thirty-Third Annual ACM Symposium on Theory of Computing, 2001.
- Berthold Vocking, "Selfish Load Balancing", Algorithmic Game Theory, Cambridge University Press, 2007.
