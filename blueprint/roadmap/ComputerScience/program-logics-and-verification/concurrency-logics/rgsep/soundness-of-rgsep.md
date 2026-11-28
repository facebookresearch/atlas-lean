# Soundness of RGSep

Every judgment derivable in the RGSep proof system is semantically valid: a derived $C\ \mathbf{sat}\ (p, \mathcal{R}, \mathcal{G}, q)$ guarantees that $C$, under interference within $\mathcal{R}$, never faults, changes shared state only within $\mathcal{G}$, and establishes $q$ on termination.

Fix a separation algebra $(M, \uplus, \emptyset)$ and a set of primitive commands, each a local relation on $M$. Use the commands and rules of [RGSep proof rules](rgsep-proof-rules.md), in which the rule Prim applies only to separation-logic triples valid for their primitive command and Atom only with the annotation of its atomic block, annotations being uniformly precise, the [operational semantics of RGSep programs over structured states](operational-semantics-of-rgsep-programs.md), and [semantic validity of RGSep judgments](semantic-validity-of-rgsep-judgments.md).

**Theorem (soundness).** If $\vdash C\ \mathbf{sat}\ (p, \mathcal{R}, \mathcal{G}, q)$, then $\models C\ \mathbf{sat}\ (p, \mathcal{R}, \mathcal{G}, q)$.

The theorem holds for every partial commutative cancellative monoid of heaps and every choice of local primitive commands. It is the thesis's Theorem 28 for this system, with two readings stated on the rules and semantics pages. Prim's premise is a valid separation-logic triple, as in the basic-action rule of the 2007 report; the thesis prints a derivable triple, and its proof of the Prim case uses only validity, so for a sound separation logic this reading admits every Prim instance of the thesis. Atomic annotations are uniformly precise and read existentially in the oracle, which is stronger than the thesis's precision for each interpretation. Loop carries the premise that its invariant is stable under the rely, which the thesis's rule does not print; the rules page gives a derivation showing that without it an invariant can fail after zero iterations. Commands outside the stated language, such as conditionals with Boolean tests, guarded atomic blocks and the concrete shared read of the conference paper, are not covered.

## Depends on

- [RGSep proof rules](rgsep-proof-rules.md)
- [Semantic validity of RGSep judgments](semantic-validity-of-rgsep-judgments.md)
- [Operational semantics of RGSep programs over structured states](operational-semantics-of-rgsep-programs.md)

## Proof depends on

- [RGSep proof rules](rgsep-proof-rules.md)
- [Semantic validity of RGSep judgments](semantic-validity-of-rgsep-judgments.md)
- [Operational semantics of RGSep programs over structured states](operational-semantics-of-rgsep-programs.md)
- [RGSep assertions over local and shared state](rgsep-assertions-over-local-and-shared-state.md)

## Expansion

The proof is by induction on derivations, one case per rule. Its prerequisites are lemmas about the operational semantics that have no pages: locality of reductions (a run from $(l_1 \uplus l', s)$ either restricts to a run from $(l_1, s)$ with $l'$ framed off, or the run from $(l_1, s)$ faults) and monotonicity of reductions in the rely; monotonicity of the guarantee predicate in the state, the rely and the guarantee; the decomposition of runs of primitive commands and atomic blocks into environment steps around one program step; the parallel decomposition, by which guarantees of $C_1$ under $R \cup G_2$ and of $C_2$ under $R \cup G_1$ give the guarantee $G_1 \cup G_2$ of $C_1 \parallel C_2$ under $R$ and runs of the composition project to runs of the components; two lemmas on sequential composition; the equivalence of $C$ and $C \parallel \mathbf{skip}$; and the fact that every derivable judgment $C\ \mathbf{sat}\ (p, \mathcal{R}, \mathcal{G}, q)$ has a derivable stronger specification with a stable precondition $p'$ implied by $p$ and a stable postcondition $q'$ implying $q$. The case Prim uses validity of the primitive triple and that environment steps do not touch the local heap; Atom uses uniform precision of the annotation to identify the oracle's split with the one obtained under the judgment's interpretation; Frame is derived from Par and Skip; Loop uses its stability premise for the zero-iteration case. The thesis reports that the rules, the semantics and these lemmas and theorems are formalized in Isabelle/HOL.

## Sources

- V. Vafeiadis, *Modular fine-grained concurrency verification*, PhD thesis, University of Cambridge, Technical Report UCAM-CL-TR-726, July 2008, <https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-726.pdf>: Section 3.3, Lemmas 20–27, Theorem 28 and its proof by cases, and footnote 2 (mechanization in Isabelle/HOL).
- V. Vafeiadis and M. Parkinson, *A marriage of rely/guarantee and separation logic*, Technical Report UCAM-CL-TR-687, University of Cambridge Computer Laboratory, June 2007, <https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-687.pdf>: Section 5, Theorem 31 and its proof (the basic-action case assumes a valid separation-logic triple for the action, and the shared-read axiom is treated separately in the concrete model).
- V. Vafeiadis and M. Parkinson, "A marriage of rely/guarantee and separation logic", *CONCUR 2007 – Concurrency Theory*, LNCS 4703, Springer, 2007, pp. 256–271, <https://doi.org/10.1007/978-3-540-74407-8_18>, author copy <https://www.mpi-sws.org/~viktor/papers/concur2007-marriage.pdf>: Section 5, Theorem 2 and footnote 7 (precision with no interpretation).
