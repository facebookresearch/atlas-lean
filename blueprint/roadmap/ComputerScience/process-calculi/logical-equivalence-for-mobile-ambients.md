# Logical equivalence for mobile ambients is undecidable

Two processes of the Ambient calculus are logically equivalent when they satisfy the same formulas of the Ambient Logic. This equivalence is undecidable on the full calculus with replication, although it is decidable on the image-finite fragment, and on a smaller syntactic subfragment it coincides with structural congruence extended by an eta law.

**Setting (Hirschkoff, Lozes and Sangiorgi).** The calculus MA (Mobile Ambients) considered here is asynchronous, communicates names only and has no restriction operator. Its processes are built from $\mathbf{0}$, parallel composition $P \mid Q$, replication $!P$, ambients $n[P]$, capability prefixes $\mathsf{in}\, n.P$, $\mathsf{out}\, n.P$ and $\mathsf{open}\, n.P$, input of a name and asynchronous output of a name; structural congruence $\equiv$ and reduction are the standard ones. The Ambient Logic AL has the propositional connectives, universal quantification over names, a temporal modality $\Diamond \mathcal{A}$ ("after some reductions, $\mathcal{A}$ holds"), the spatial connectives $\mathbf{0}$, $\mathcal{A} \mid \mathcal{B}$ and $n[\mathcal{A}]$, and their adjuncts $\mathcal{A} \triangleright \mathcal{B}$ and $\mathcal{A} @ n$; for example, $P \models \mathcal{A}_1 \mid \mathcal{A}_2$ when $P \equiv P_1 \mid P_2$ with $P_i \models \mathcal{A}_i$. Closed processes $P$ and $Q$ are *logically equivalent*, $P =_L Q$, if they satisfy the same closed formulas.

**Theorem (Hirschkoff, Lozes and Sangiorgi).** Logical equivalence $=_L$ is an undecidable relation on MA.

On the image-finite fragment $\mathrm{MA}_{\mathrm{IF}}$, the same paper derives decidability of $=_L$ from its inductive characterization, which holds on all of MA (Corollary 4.20). On the syntactic subfragment $\mathrm{MA}_{\mathrm{sIF}}$ (Definition 5.2) it shows that $=_L$ coincides with structural congruence extended by the eta law (Corollary 5.10), and notes that this approach does not apply to $\mathrm{MA}_{\mathrm{IF}}$.

## Depends on

- [Decidability by multi-stack machines](../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Halting is undecidable](../../TheoryOfComputation/computability/halting-problem-and-rice-s-theorem/not-tm2-decidable-halts.md)

## Expansion

The proof encodes Turing machines in the syntactic image-finite fragment of MA, representing the tape as a ribbon of ambients and simulating each transition by a sequence of reductions. The construction yields processes $P_0$ and $P_1$, built from a machine $\mathcal{M}$ and a word $w$ and differing in the length of a growing ribbon, such that $P_0$ always reduces to $P_1$, while $P_1$ reduces to $P_0$ exactly when $\mathcal{M}$ accepts $w$ on some finite, sufficiently long tape. The authors show that $\mathsf{open}\, n.P_0 =_L \mathsf{open}\, n.P_1$ holds exactly when $P_0$ and $P_1$ reduce to each other, so deciding logical equivalence would decide acceptance. A good expansion links a page for the encoding of Turing machines in mobile ambients and its correctness lemma.

## Sources

- Daniel Hirschkoff, Étienne Lozes and Davide Sangiorgi, *Separability in the Ambient Logic*, Logical Methods in Computer Science 4(3), 2008, https://doi.org/10.2168/LMCS-4(3:4)2008; the syntax of MA and the Ambient Logic, the satisfaction relation, and the undecidability theorem for logical equivalence in the section on undecidability, read in arXiv:0806.3849v2. Locators in arXiv:0806.3849v2: Corollary 4.20, Definition 5.2, Corollary 5.10 and Theorem 6.14.
