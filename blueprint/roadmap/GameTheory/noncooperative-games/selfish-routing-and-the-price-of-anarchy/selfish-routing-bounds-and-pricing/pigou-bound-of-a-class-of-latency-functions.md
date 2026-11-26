# Pigou bound of a class of latency functions

For a class $\mathcal{C}$ of nonnegative continuous nondecreasing latency functions, the *Pigou bound* is

$$
\alpha(\mathcal C) = \sup_{c \in \mathcal C}\ \sup_{r \ge 0}\ \sup_{x \ge 0} \frac{r\, c(r)}{x\, c(x) + (r - x)\, c(r)} \in [1, \infty],
$$

the worst ratio between the equilibrium and the cost of an arbitrary split in a two-link Pigou network routing $r$ units over a link with latency $c$ and a link with constant latency $c(r)$.

## Depends on

- [Pigou's network](../pigou.md)
- [Nonatomic routing instance](../routing-instance.md)

## Sources

- Tim Roughgarden, "The Price of Anarchy is Independent of the Network Topology", Journal of Computer and System Sciences, 2003.
- Tim Roughgarden, "CS364A: Algorithmic Game Theory, Lecture Notes", Stanford University, Fall 2013, 2013.
