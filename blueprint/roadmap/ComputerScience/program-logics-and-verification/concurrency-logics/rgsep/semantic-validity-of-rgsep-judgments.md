# Semantic validity of RGSep judgments

An RGSep judgment is defined to be valid when, from every state satisfying its precondition under any smaller rely, every program step stays within the guarantee, no step faults, and every terminating run ends in a state satisfying the postcondition.

Use structured heaps $\sigma = (l, s, o)$ and the labelled reduction $(C, \sigma) \xrightarrow{R}_{\lambda} \mathit{Config}$ of the [operational semantics of RGSep programs](operational-semantics-of-rgsep-programs.md).

The *guarantee* predicate is defined by induction on $n$: $(C, \sigma, R)\ \mathrm{guars}_0\ G$ always holds, and $(C, \sigma, R)\ \mathrm{guars}_{n+1}\ G$ holds iff every reduction $(C, \sigma) \xrightarrow{R}_{\lambda} \mathit{Config}$ has $\mathit{Config} = (C', \sigma')$ with $(C', \sigma', R)\ \mathrm{guars}_n\ G$, and $(\sigma, \sigma') \in G$ when $\lambda = p$. In particular no step faults.

The judgment $\models C\ \mathbf{sat}\ (p, \mathcal{R}, \mathcal{G}, q)$ holds iff for every set of actions $\mathcal{R}' \subseteq \mathcal{R}$ and every structured heap $\sigma = (l, s, o)$ and interpretation $i$ with $l, s, i \models_{\mathcal{R}'} p$:

1. $(C, \sigma, [\![\mathcal{R}']\!])\ \mathrm{guars}_n\ [\![\mathcal{G}]\!]$ for every $n$, where $(\sigma, \sigma') \in [\![\mathcal{G}]\!]$ compares the shared components of $\sigma$ and $\sigma'$, as in the thesis's Definition 18 (condition 3) and the 2007 report's proof of Theorem 31; and
2. if $(C, \sigma)$ reaches $(\mathbf{skip}, (l', s', o'))$ by finitely many $[\![\mathcal{R}']\!]$-reductions, then $l', s', i \models_{\mathcal{R}'} q$.

Assertions are [RGSep assertions](rgsep-assertions-over-local-and-shared-state.md) and actions those of [actions and interference in RGSep](rgsep-actions-and-interference.md); assertions ignore the environment part $o$.

## Depends on

- [Operational semantics of RGSep programs over structured heaps](operational-semantics-of-rgsep-programs.md)
- [RGSep assertions over local and shared state](rgsep-assertions-over-local-and-shared-state.md)
- [Actions and interference in RGSep](rgsep-actions-and-interference.md)

## Proof depends on

None.

## Expansion

With procedures, the technical report indexes validity by a step count $n$ and a procedure context (Definitions 28–30). A development needs the operational semantics page and the satisfaction relation of RGSep assertions on structured heaps, which ignores the environment part.

## Sources

- V. Vafeiadis and M. Parkinson, "A marriage of rely/guarantee and separation logic", *CONCUR 2007 – Concurrency Theory*, LNCS 4703, Springer, 2007, pp. 256–271, <https://doi.org/10.1007/978-3-540-74407-8_18>, author copy <https://www.mpi-sws.org/~viktor/papers/concur2007-marriage.pdf>: Section 5 (Definitions 7 and 8; footnote 6, assertions ignore the environment).
- V. Vafeiadis and M. Parkinson, *A marriage of rely/guarantee and separation logic*, Technical Report UCAM-CL-TR-687, University of Cambridge Computer Laboratory, June 2007, <https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-687.pdf>: Section 5 (Definitions 18 and 28–30, and the proof of Theorem 31).
- V. Vafeiadis, *Modular fine-grained concurrency verification*, PhD thesis, University of Cambridge, Technical Report UCAM-CL-TR-726, July 2008, <https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-726.pdf>: Section 3.3, Definition 18 (the guarantee: no failure, and every shared-state change of a program step satisfies the guarantee).
