# Expected pre-speciation mutations on a four-leaf duplication–speciation tree

**F-tree.** A duplication creates paralogous sites $x, y$; a later speciation yields orthologs $x_1, x_2$ and $y_1, y_2$. The *F-tree* has a root (the duplication), a left child with leaves $A, C$ and a right child with leaves $B, D$, where $A, B, C, D \subseteq \{a,c,g,t\}$ are the leaf label sets of $x_1, y_1, x_2, y_2$; the two internal edges below the root precede speciation. Fitch sets are $L = A\cap C$ if nonempty, else $A \cup C$; $R = B \cap D$ if nonempty, else $B\cup D$; $X = L\cap R$ if nonempty, else $L\cup R$. The number $N$ of unions used is the minimum number of mutations. A *labeling* assigns one nucleotide from its set to each leaf and any nucleotides to the internal nodes so that exactly $N$ edges change label. Let $N_b$ be the average, over all labelings, of the number of mutations on the two edges below the root, and $N_a = N - N_b$.

**Singleton leaves.** When $A, B, C, D$ are singletons, every motif $x_1 y_1 x_2 y_2$ falls into one of seven classes, represented by $aaaa$, $aaat$, $atta$, $caat$, $tata$, $acat$, $actg$:

| motif | $N$ | labelings | $N_b$ |
|---|---|---|---|
| $aaaa$, $aaat$, $atta$, $caat$ | $0,1,2,2$ | all after speciation | $0$ |
| $tata$ (orthologs equal in pairs) | $1$ | $2$ | $1$ |
| $acat$ | $2$ | $5$ | $4/5$ |
| $actg$ | $3$ | $12$ | $2/3$ |

**General sets.** Let $n_{\mathrm{motif}}$ count the leaf assignments $(x_1,y_1,x_2,y_2) \in A\times B\times C\times D$ of each motif class that achieve $N$ mutations. Then

- if $N = 1$: $\ N_b = \dfrac{2n_{tata}}{2n_{tata} + n_{aaat}}$;
- if $N = 2$: $\ N_b = \dfrac{4n_{acat}}{5n_{acat} + 2n_{atta} + n_{caat}}$;
- if $N = 3$: $\ N_b = 2/3$ (this forces all four sets to be singletons).

## Expansion

Each class contributes its number of minimal labelings, weighted by how many of them put mutations on the pre-speciation edges: a $tata$ motif has two minimal labelings, both with the single mutation above the speciation, while an $aaat$ motif has one labeling with the mutation on a leaf edge. For $N = 2$ the $acat$ motif contributes five labelings, four of them with a mutation before speciation, and $atta$ and $caat$ contribute two and one labelings with both mutations after. $N = 3$ requires $A\cap C$, $B \cap D$ and $(A\cup C)\cap(B\cup D)$ all empty, which forces singletons. Applied to the 11-residue repeats of phage tape measure proteins, a large $N_b$ indicates that most divergence between paralogous units predates the divergence of the phage lineages.

## Depends on

- [Fitch's algorithm](../../small-parsimony-problem/fitch.md)

## Sources

- Belcaid M, Bergeron A, Poisson G, "The evolution of the tape measure protein: units, duplications and losses", BMC Bioinformatics (2011), Definition 1, Problem 1 and Lemmas 1–3, <https://doi.org/10.1186/1471-2105-12-s9-s10>, PMCID PMC3271669.
