# Janson's inequalities

A random subset $R$ of a finite ground set contains each element independently; for sets $S_1, \dots, S_k$, Janson's inequalities bound the probability that no $S_i$ is contained in $R$ by $e^{-\mu + \Delta/2}$, and by $e^{-\mu^2/(2\Delta)}$ when $\Delta \ge \mu$. They give exponentially small non-existence probabilities where the second moment method gives only polynomial ones; with $G(n,p)$ as the random subset of the edges of $K_n$ they bound, for example, the probability that $G(n,p)$ is triangle-free.

- [Law of a random subset with independent elements](random-subset-law.md)
- [The event that a random subset contains a given set](contains-event.md)
- [Probability that a random subset contains a given set](random-subset-law-real-contains-event.md)
- [Expected number of contained sets (Janson's μ)](janson-mu.md)
- [Janson's correlation sum Δ](janson-delta.md)
- [First Janson inequality](janson-inequality.md)
- [Second Janson inequality](janson-inequality-of-le.md)
- [The event that a random subset avoids a given set](avoid-event.md)
- [Probability that a random subset avoids a given set](random-subset-law-real-avoid-event.md)

## Related topics

- [First and second moment methods](../first-and-second-moment-methods/README.md): the polynomial counterpart of Janson's bound.
- [Harris inequality](../../../Probability/correlation-inequalities/harris-fkg-bk/harris-inequality/README.md): the lower bound $\Pr[\text{no } A_i] \ge \prod_i (1 - \Pr[A_i])$ and the key step of the proof of the first Janson inequality.
- [Symmetric Lovász Local Lemma](../lovasz-local-lemma-symmetric-finite.md): another bound on the probability that none of a family of mostly independent bad events occurs, positive rather than small.

- [Probability that a random subset equals a given subset](random-subset-law-real-singleton.md)
