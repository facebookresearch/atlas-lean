# Unique algebraic tree of an RNA secondary structure

**Setting.** An RNA secondary structure $S$ is a sequence over $\{A, C, G, U\}$ together with a non-empty set of weak interactions (base pairs) in which each nucleotide takes part in at most one pair; pairs may cross (pseudoknots). A *hairpin* is a single base pair closing a run of unpaired nucleotides; a *pseudoloop* $(a_1^\bullet, a_N^\bullet)\langle a_2 \cdots a_{N-1}\rangle$ is a structure segment delimited by two paired nucleotides, with the state $\bullet$ (paired) or $\circ$ (unpaired) recorded for each interior nucleotide. Three operators combine pseudoloops:

- *concatenation* $P_1 \odot_\eta P_2$: join $P_1$ and $P_2$ by a possibly empty run $\eta$ of unpaired nucleotides;
- *nesting*: place a pseudoloop inside an enclosing pair;
- *crossing* $P_1 \bowtie_k P_2$: overlap a proper suffix of $P_1$, starting at its position $k$, with a proper prefix of $P_2$ so that $P_2$ ends after $P_1$, defined only when shared nucleotides still take part in at most one pair.

A regular tree grammar $G_{RNA}$ over these operators, with hairpins as base cases and an unpaired *head* and *tail* attached at the ends, derives *algebraic RNA trees*.

**Theorem.**

1. Every RNA secondary structure $S$ has exactly one derived tree of $G_{RNA}$.
2. Conversely, every derived tree of $G_{RNA}$ corresponds to an RNA secondary structure.
3. $S$ is pseudoknotted if and only if its derived tree has an internal node labelled with the crossing operator $\bowtie$.

**Corollary.** Every secondary structure decomposes uniquely into hairpins combined by concatenation, nesting and crossing, together with a head and a tail.

Forgetting the primary sequence in the algebraic tree gives a *structural RNA tree*; the classical tree alignment distance $d_T(t_1, t_2) = \min\{\sigma(\mathcal L)\}$ over alignments $\mathcal L$ of two such trees then defines a similarity measure for RNA structures with arbitrary pseudoknots.

## Depends on

- [Bottom-up finite tree automata](../../../../TheoryOfComputation/omega-automata-and-games/logic-and-tree-automata/bottom-up-finite-tree-automata.md)

## Expansion

The proof of uniqueness parses a structure from left to right, identifying hairpins and deciding at each step which operator joins the current pseudoloop with the next hairpin; crossing is selected only when the rightmost hairpin actually crosses a pair of the pseudoloop on its left. The grammar's conditional productions encode the well-definedness side conditions of crossing, so every derivation spells a valid structure. Pseudoknot-free structures never use $\bowtie$ and reduce to the usual tree representation.

## Sources

- M. Quadrini, L. Tesei and E. Merelli, "An algebraic language for RNA pseudoknots comparison", *BMC Bioinformatics* (2019), Definitions 1–8, Theorems 1–3 and Corollary 1. <https://doi.org/10.1186/s12859-019-2689-5> (PMC6471698)
