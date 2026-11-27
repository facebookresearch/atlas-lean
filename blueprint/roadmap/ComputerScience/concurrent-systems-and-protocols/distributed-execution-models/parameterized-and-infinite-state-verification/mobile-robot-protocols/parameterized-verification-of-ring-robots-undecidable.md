# Parameterized verification of oblivious robots on a ring is undecidable

Protocols for a fixed number of oblivious mobile robots on rings of unknown size can be written as Presburger formulas over each robot's view of the distances to the others. Whether some ring size and starting configuration lead to a bad configuration is undecidable under the asynchronous scheduler, and the paper's reachability variant is undecidable under all three schedulers.

**Setting (Sangnier, Sznajder, Potop-Butucaru and Tixeuil).** Fix $k$ robots. On a ring of size $n \ge k$ with positions $0, \dots, n-1$ numbered clockwise, a *$(k, n)$-configuration* gives each robot's position. The *view* of a robot lists the clockwise distances between successive robots starting from its next occupied neighbor, a tuple $(d_1, \dots, d_k)$ with $d_1 \ne 0$ and $\sum d_i = n$; the view in the opposite direction is its reversal. A *protocol* is a quantifier-free Presburger formula $\phi(x_1, \dots, x_k)$ such that whenever a view satisfies $\phi$ and differs from its reversal, the reversal does not satisfy $\phi$: a robot moves one step clockwise if its clockwise view satisfies $\phi$, one step counterclockwise if its counterclockwise view does, either way if both views coincide and satisfy $\phi$, and stays otherwise. In the *synchronous* mode all robots act at once; in the *semi-synchronous* mode an arbitrary subset does; in the *asynchronous* mode one robot at a time either looks (records its current view) or moves according to its last recorded view. Ring sizes and configurations are specified by quantifier-free Presburger formulas $\mathtt{Ring}(y)$, $\mathtt{Bad}(x_1, \dots, x_k)$ and $\mathtt{Goal}(x_1, \dots, x_k)$. For a mode $m$, the problem $\mathrm{SAFETY}_m$ asks whether there are a size $n$ satisfying $\mathtt{Ring}$ and a configuration outside $\mathtt{Bad}$ from which a configuration in $\mathtt{Bad}$ is reachable; $\mathrm{REACHABILITY}_m$ asks whether there are a size $n$ satisfying $\mathtt{Ring}$ and a configuration from which no configuration in $\mathtt{Goal}$ is reachable.

**Theorem (Sangnier, Sznajder, Potop-Butucaru and Tixeuil).**

1. $\mathrm{SAFETY}$ in the asynchronous mode is undecidable.
2. $\mathrm{REACHABILITY}$ is undecidable in each of the synchronous, semi-synchronous and asynchronous modes.

When at most one robot can move in any configuration, the three semantics have the same reachable configurations; the same paper shows that safety is decidable in the synchronous and semi-synchronous modes, by reduction to satisfiability of existential Presburger formulas.

## Depends on

None.

## Proof depends on

- [Two-counter machines are universal](../../../../../TheoryOfComputation/equivalence-of-models/counter-machines/two-counter-machines-are-universal.md)

## Expansion

Both proofs encode runs of deterministic counter machines. The distances between robots on the ring store the machine's control state and counter values, so that a configuration of the robots of a special "machine-like" shape represents a machine configuration, and the protocol makes the robots move so that successive machine-like configurations follow the machine's transitions. In the asynchronous case, a bad configuration becomes reachable from a configuration encoding the initial machine configuration exactly when the machine halts; because the ring size is existentially quantified, a large enough ring holds any finite computation.

## Sources

- Arnaud Sangnier, Nathalie Sznajder, Maria Potop-Butucaru and Sébastien Tixeuil, "Parameterized verification of algorithms for oblivious robots on a ring", Formal Methods in Computer-Aided Design (FMCAD 2017), pp. 212–219, 2017, <https://doi.org/10.23919/FMCAD.2017.8102262>; journal version Formal Methods in System Design 56, pp. 55–89, 2019, <https://doi.org/10.1007/s10703-019-00335-y>; Section 2 (the formal model, protocols and the three semantics, the two problems), Theorem 2 and Theorem 3 (main statement) of Section 3, and Theorem 1 of arXiv:1706.05193v1, read at <https://arxiv.org/abs/1706.05193v1>.
