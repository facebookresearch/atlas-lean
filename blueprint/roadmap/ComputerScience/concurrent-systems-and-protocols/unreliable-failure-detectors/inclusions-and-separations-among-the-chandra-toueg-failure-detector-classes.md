# Inclusions and separations among the Chandra–Toueg failure detector classes

Over failure patterns (monotone crash sets over discrete time) and suspect-set histories, the eight classes of Chandra and Toueg (perfect $\mathcal P$, quasi-perfect $\mathcal Q$, strong $\mathcal S$, weak $\mathcal W$ and their eventual versions $\Diamond\mathcal P, \Diamond\mathcal Q, \Diamond\mathcal S, \Diamond\mathcal W$), defined by strong or weak completeness combined with strong, weak, eventual strong or eventual weak accuracy, satisfy the evident inclusions ($\mathcal P \subseteq \mathcal S \subseteq \Diamond\mathcal S$, $\mathcal P \subseteq \Diamond \mathcal P$, etc.), and the inclusions are strict: for example some eventually perfect history is not weakly accurate, some strong history is not eventually strongly accurate, and some quasi-perfect history is not strongly complete. With at most two processes weak and strong completeness coincide.

## Proof sketch

Inclusions follow by unfolding the completeness and accuracy properties; separations are explicit histories, e.g. suspecting a correct process for finitely many steps breaks perpetual accuracy but not eventual accuracy.

## Depends on

- [Failure detector classes](../consensus-and-agreement/failure-detector-classes.md)

## Sources

- Tushar Deepak Chandra and Sam Toueg, "Unreliable Failure Detectors for Reliable Distributed Systems", Journal of the ACM, 1996.
