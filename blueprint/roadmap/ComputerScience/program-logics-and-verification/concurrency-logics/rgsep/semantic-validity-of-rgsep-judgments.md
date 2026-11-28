# Semantic validity of RGSep judgments

An RGSep judgment is defined to be valid when, from every state satisfying its precondition, no execution under the rely faults, every program step changes the shared state only within the guarantee, and every terminating execution ends in a state satisfying the postcondition.

Use structured states $\sigma = (l, s)$ and the labelled reduction $(C, \sigma) \xrightarrow{R}_{\lambda} \mathit{Config}$ of the [operational semantics of RGSep programs](operational-semantics-of-rgsep-programs.md), [RGSep assertions](rgsep-assertions-over-local-and-shared-state.md) and the meaning $[\![\cdot]\!]$ of sets of actions from [actions and interference in RGSep](rgsep-actions-and-interference.md).

For relations $R$ and $G$ on $M$, the predicate $(C, \sigma, R)$ *guarantees* $G$ holds if $(C, \sigma, R)$ guarantees$_n$ $G$ for every $n$, where guarantees$_0$ always holds, and $(C, (l, s), R)$ guarantees$_{n+1}$ $G$ holds iff every reduction $(C, (l, s)) \xrightarrow{R}_{\lambda} \mathit{Config}$ has

1. $\mathit{Config} = (C', (l', s'))$ for some $C', l', s'$;
2. $(C', (l', s'), R)$ guarantees$_n$ $G$; and
3. $(s, s') \in G$ if $\lambda = p$.

The judgment $\models C\ \mathbf{sat}\ (p, \mathcal{R}, \mathcal{G}, q)$ holds iff for all $l, s$ and interpretations $i$ with $l, s, i \models p$:

1. $(C, (l, s), [\![\mathcal{R}]\!])$ guarantees $[\![\mathcal{G}]\!]$; and
2. if $(C, (l, s))$ reaches $(\mathbf{skip}, (l', s'))$ by zero or more $[\![\mathcal{R}]\!]$-reductions, then $l', s', i \models q$.

## Depends on

- [Operational semantics of RGSep programs over structured states](operational-semantics-of-rgsep-programs.md)
- [RGSep assertions over local and shared state](rgsep-assertions-over-local-and-shared-state.md)
- [Actions and interference in RGSep](rgsep-actions-and-interference.md)

## Proof depends on

None.

## Expansion

The guarantee compares the shared components before and after each program step; environment steps are unconstrained by it. The conference paper and its report state validity over three-component states, quantified over every sub-rely and, with procedures, indexed by a step count.

## Sources

- V. Vafeiadis, *Modular fine-grained concurrency verification*, PhD thesis, University of Cambridge, Technical Report UCAM-CL-TR-726, July 2008, <https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-726.pdf>: Section 3.3, Definition 18 (guarantees) and Definition 19 (validity).
- V. Vafeiadis and M. Parkinson, "A marriage of rely/guarantee and separation logic", *CONCUR 2007 – Concurrency Theory*, LNCS 4703, Springer, 2007, pp. 256–271, <https://doi.org/10.1007/978-3-540-74407-8_18>, author copy <https://www.mpi-sws.org/~viktor/papers/concur2007-marriage.pdf>: Section 5, Definitions 7 and 8 (the three-component variant).
- V. Vafeiadis and M. Parkinson, *A marriage of rely/guarantee and separation logic*, Technical Report UCAM-CL-TR-687, University of Cambridge Computer Laboratory, June 2007, <https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-687.pdf>: Section 5, Definitions 18 and 28–30 (the step-indexed variant with procedures).
