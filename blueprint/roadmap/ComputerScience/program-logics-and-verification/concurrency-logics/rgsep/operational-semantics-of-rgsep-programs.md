# Operational semantics of RGSep programs over structured states

RGSep programs run on structured states that split the heap into the thread's local part and the shared part. Primitive commands act on the local part only, atomic blocks merge local and shared state and split it again by their annotation, and environment steps change the shared part within a rely relation.

Use the commands, primitive commands and annotated atomic blocks $\langle C \rangle_{P \rightsquigarrow Q}$ of [RGSep proof rules](rgsep-proof-rules.md), over the separation algebra $(M, \uplus, \emptyset)$. A *structured state* is a pair $\sigma = (l, s)$ of a local heap $l$ and a shared heap $s$ with $l \uplus s$ defined, and $(l_1, s) \uplus (l_2, s) = (l_1 \uplus l_2, s)$ when $l_1 \uplus l_2 \uplus s$ is defined, so that the result is again a structured state; the composition is undefined otherwise, in particular for different shared parts. For uniformly precise annotations $P$ and $Q$ (as on the proof-rules page), the *oracle* is the partial function

$$\mathrm{oracle}_{P \rightsquigarrow Q}(s, l) = (l', s_0 \uplus s_2) \quad \text{if } s = s_1 \uplus s_0,\ s_1 \models_{SL} P,\ l = l' \uplus s_0 \uplus s_2 \text{ and } s_2 \models_{SL} Q,$$

undefined if there are no such $s_1, s_0, s_2, l'$, where $s_1 \models_{SL} P$ means $s_1, i \models_{SL} P$ for some interpretation $i$, and likewise for $Q$; uniform precision makes $s_1$, $s_0$, $s_2$ and $l'$ unique. This existential reading of the annotations is the page's reading: the source prints the oracle with $\models_{SL}$ and no interpretation. For a relation $R$ on $M$, a configuration is $\mathrm{fault}$ or a pair $(C, \sigma)$, and $(C, \sigma) \xrightarrow{R}_{\lambda} \mathit{Config}$, with label $\lambda = p$ for a program step and $\lambda = e$ for an environment step, is the least relation closed under:

- *atomic blocks*: if $(C, (l \uplus s, \emptyset))$ reaches $(\mathbf{skip}, (l_2, \emptyset))$ in zero or more steps with the empty rely, then $\langle C \rangle_{P \rightsquigarrow Q}$ steps by a program step from $(l, s)$ to $(\mathbf{skip}, (l', s'))$ if $\mathrm{oracle}_{P \rightsquigarrow Q}(s, l_2) = (l', s')$, and to $\mathrm{fault}$ if it is undefined; if $(C, (l \uplus s, \emptyset))$ reaches $\mathrm{fault}$ with the empty rely, the block steps to $\mathrm{fault}$;
- *primitive commands*: $c$ steps from $(l, s)$ to $(\mathbf{skip}, (l', s))$ if $c(l, l')$ and $l' \uplus s$ is defined, and to $\mathrm{fault}$ if $c$ faults at $l$;
- *environment*: $(C, (l, s)) \xrightarrow{R}_{e} (C, (l, s'))$ whenever $(s, s') \in R$ and $l \uplus s'$ is defined;
- *control*: $\mathbf{skip} ; C$ steps to $C$; $C ; C'$ steps to $C_1 ; C'$ when $C$ steps to $C_1$; $C_1 + C_2$ steps to $C_1$ and to $C_2$; $C^\ast$ steps to $\mathbf{skip} + (C ; C^\ast)$; $\mathbf{skip} \parallel \mathbf{skip}$ steps to $\mathbf{skip}$; $C_1 \parallel C_2$ steps when either component does; and a fault of $C$ makes $C ; C_2$, $C \parallel C_2$ and $C_2 \parallel C$ fault. These are program steps that leave the state unchanged, except those inherited from a component's step.

An atomic block whose body has no terminating and no faulting run with the empty rely has no transition; in particular a diverging body is not a splitting fault.

## Depends on

- [RGSep proof rules](rgsep-proof-rules.md)
- [Precise predicates](../../separation-logic-metatheory/abstract-separation-logic/precise-predicates.md)

## Proof depends on

None.

## Expansion

Definedness of $l_1 \uplus s$, $l_2 \uplus s$ and $l_1 \uplus l_2$ separately does not give definedness of $l_1 \uplus l_2 \uplus s$ in every separation algebra: with fractional permissions, three portions $0.4$ of one cell are pairwise compatible but not jointly. The thesis defines the composition of structured states by agreement of the shared parts (its Definition 17) and requires states to be structured (its Definition 16); the condition above makes that requirement explicit. Ignoring the split of the state gives the plain interleaving semantics of the language. Uniform precision of the annotation is what makes the oracle a function; precision for each interpretation separately does not, since two interpretations can select different splits. The conference paper and its report use a three-component state with the other threads' heaps and annotate atomic blocks by a single precise postcondition; the thesis's two-component formulation is the one used with the rules and validity here.

## Sources

- V. Vafeiadis, *Modular fine-grained concurrency verification*, PhD thesis, University of Cambridge, Technical Report UCAM-CL-TR-726, July 2008, <https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-726.pdf>: Section 2.2 (Figure 2.1 and the discussion of atomic blocks with diverging bodies) and Section 3.2 (Figure 3.2, Definitions 16 and 17 (structured states and their composition), the oracle printed with $s_1 \models_{SL} P$ and no interpretation, and the explanation of the rules for atomic blocks, primitive commands and environment steps) and Section 3.3 (the proof of Theorem 28, atomic case, which identifies the split under the judgment's interpretation).
- V. Vafeiadis and M. Parkinson, "A marriage of rely/guarantee and separation logic", *CONCUR 2007 – Concurrency Theory*, LNCS 4703, Springer, 2007, pp. 256–271, <https://doi.org/10.1007/978-3-540-74407-8_18>, author copy <https://www.mpi-sws.org/~viktor/papers/concur2007-marriage.pdf>: Section 5 (Definitions 5 and 6, Fig. 4: the three-component variant; footnote 7, precise assertions defined with no interpretation).
