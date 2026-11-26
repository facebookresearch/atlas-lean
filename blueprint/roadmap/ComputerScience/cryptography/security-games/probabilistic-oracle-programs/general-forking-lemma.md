# General forking lemma

Let $P$ be an oracle program making at most $q$ queries with answers in a set of size $h$, with acceptance probability $\mathrm{acc}$. Then the forking algorithm succeeds with probability

$$\mathrm{frk} \ge \mathrm{acc}\left(\frac{\mathrm{acc}}{q} - \frac{1}{h}\right).$$

## Proof sketch

Condition on the coins, the answer prefix and the named index $J = j$. By Jensen's inequality (Cauchy–Schwarz) the probability that two runs sharing everything before position $j$ both name $j$ is at least the square of the probability for one run; summing over $j$ and using $\sum_j a_j^2 \ge (\sum_j a_j)^2/q$ gives $\mathrm{acc}^2/q$, and the event $h_J = h'_J$ costs at most $\mathrm{acc}/h$.

## Depends on

- [Forking an oracle program at a named query](forking-algorithm.md)

## Proof depends on

- [The rewinding lemma](../../signatures-and-protocols/zero-knowledge-and-arguments/the-rewinding-lemma.md)

## Sources

- M. Bellare and G. Neven, "Multi-Signatures in the Plain Public-Key Model and a General Forking Lemma", Proceedings of the 13th ACM Conference on Computer and Communications Security (CCS), 2006.
- D. Pointcheval and J. Stern, "Security Arguments for Digital Signatures and Blind Signatures", Journal of Cryptology 13(3), 2000.
