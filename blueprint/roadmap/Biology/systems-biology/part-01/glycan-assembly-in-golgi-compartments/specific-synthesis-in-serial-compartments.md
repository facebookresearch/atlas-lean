# Specific synthesis in serial compartments

**Setting.** Use the assembly-line model of [runaway and divergent reactions](runaway-and-divergent-reactions-in-assembly-lines.md): oligomers are rooted monomer trees, each compartment holds a set of glycosyltransferase enzymes and has residence time $T$, and the output oligomers of one compartment are the inputs of the next. A target oligomer is **specifically synthesizable** from an input oligomer in $N$ compartments if some series of $N$ compartments converts the input into the target as the unique final output (no byproducts), in the limit of long residence times. A compartment is **algorithmic** if it has no linkage loops and no acceptor blocks; then every input has a finite reaction network with a single terminal oligomer. A **growth order** is a sequence of single-monomer additions from input to target; it is **algorithmic** if it can occur in an algorithmic compartment, which means:
- *context-free enzymes:* identical empty branches of identical monomers are identically extended;
- *branch-sensitive enzymes:* identical empty branches of identically branched monomers are identically extended, and growth is depth-first;
- *root-sensitive enzymes:* every growth order is algorithmic.

**Lemma 5.** A target is specifically synthesizable from an input in a single compartment if and only if there is an algorithmic growth order from the input to the target.

**Theorem 1.** A target is specifically synthesizable from an input (in some number of compartments) if and only if it is specifically synthesizable from that input in a series of single-enzyme compartments.

**Theorem 2.** A target is specifically synthesizable from an input in $N$ compartments if and only if some growth order from the input to the target decomposes into $N$ consecutive algorithmic stretches.

Hence the minimum number of compartments is the minimum number of algorithmic stretches over growth orders, computable by a shortest-path search over sub-oligomers of the target; with root-sensitive enzymes one compartment always suffices, while with more promiscuous enzymes some targets need two or more compartments and some cannot be made without byproducts at all.

## Expansion

Lemma 3 (pruning): if a compartment's reaction network from an input is finite but has several terminal oligomers, removing enzymes that are blocked along some growth order eliminates every acceptor block while retaining a growth order to one of the original terminal oligomers; the pruned compartment is algorithmic. Lemma 5 then follows: a specific single-compartment synthesis has no linkage loops, pruning gives an algorithmic compartment, and its growth orders are algorithmic; conversely, the enzymes used by an algorithmic growth order create no bidirectional block (identical branches are extended identically), no unidirectional block (depth-first growth), and no loop (the target's empty branches are terminal).

Theorems 1 and 2: starting from any specific $N$-compartment synthesis, send residence times to infinity, prune each compartment to an algorithmic subset (Lemma 3), and keep a growth order through one terminal oligomer of each compartment. Within an algorithmic compartment the enzymes may act in any order, in particular one enzyme at a time on all its available sites, so each compartment can be replaced by a series of single-enzyme compartments (Theorem 1). Every growth order inside an algorithmic compartment is algorithmic, giving $N$ algorithmic stretches; conversely each algorithmic stretch is realizable in one compartment by Lemma 5 (Theorem 2).

## Depends on

- [Runaway and divergent reactions in enzymatic assembly lines](runaway-and-divergent-reactions-in-assembly-lines.md)

## Sources

- A. Jaiman, M. Thattai, "Golgi compartments enable controlled biomolecular assembly using promiscuous enzymes", eLife 9 (2020) e49573, Appendix 2 (Lemmas 3–5, Theorems 1–2), <https://doi.org/10.7554/eLife.49573>, PMCID PMC7360365.
