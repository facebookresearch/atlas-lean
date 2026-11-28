# Rank deficiency of the nearest-neighbor stacking matrix

For DNA polymers without end effects, the counts of the ten Watson–Crick nearest-neighbor doublets satisfy two independent linear constraints, so any stacking matrix of such sequences has rank at most eight: at most eight independent linear combinations of the ten doublet parameters can be determined, and exactly eight when the design spans the constrained space.

**Setting.** For a data set of $M$ duplex sequences, the stacking matrix $S\in\mathbb Z^{M\times N}$ has one row per sequence and one column per model parameter, the entry being the number of occurrences of that parameter's unit in the sequence. For the [nearest-neighbor model](nearest-neighbor-model-of-duplex-stability.md) the columns are the ten Watson–Crick doublets (plus initiation columns for oligonucleotide duplexes). A measured property (such as $\Delta G^\circ_{37}$, $\Delta H^\circ$ or $\Delta S^\circ$), after subtracting any known contribution not represented by a column (such as the symmetry term for self-complementary duplexes), is denoted $P$ and modelled as $P=S\,p$ for a parameter vector $p$; the rank statements below concern the design matrix $S$. Polymers are idealized as cyclic sequences (no ends).

**Statement.**

1. For a cyclic (end-free) sequence with $N_{xy}$ the number of occurrences of the dinucleotide $xy$ along one strand, the single-strand composition closure relations

$$\sum_{b\in\{A,T,C,G\}}\big(N_{xb}-N_{bx}\big)=0\qquad(x\in\{A,T,C,G\})$$

hold, any three of them being independent (Licinio and Guerra, Eq. 6). For double strands the ten conjugated doublet counts are linked through the two independent relations with $x=A$ and $x=G$ (their Eq. 9), so that only eight independent parameter combinations remain. Hence every stacking matrix of cyclic sequences has rank at most $8$.

2. The rank of $S$ is the number of independent linear functions of $p$ that the data determine: the data fix $Sp$, and the set of parameter vectors consistent with exact data (or the least-squares solution set) is an affine translate of $\ker S$. Rank $8$ is attained by suitable designs (the source quotes eight linearly independent sequences of Vologodskii et al.); a smaller or unlucky design has lower rank (a single sequence has rank at most $1$).
3. For a polymer design of rank $8$, the ten doublet parameters are determined only up to the two-dimensional null space given by the relations of item 1 expressed in the ten doublet counts (written out in Expansion): adding a null-space vector changes individual doublet values but leaves every polymer prediction $Sp$ unchanged. The singular-value-decomposition (minimum-norm) solution is one canonical choice. The source (SantaLucia) states that $AA/TT$ and $GG/CC$ are uniquely determined by such a design; in the class form below the null vectors indeed have zero $AA/TT$ and $GG/CC$ components.

Sequences with ends need not satisfy the two relations of item 1 (for a linear top strand the telescoping sum equals $g(\text{first base})-g(\text{last base})$): the source reports nine determinable invariants for dumbbells with fixed termini, and full rank for the ten doublets plus initiation parameters is attainable for oligonucleotides. Determinacy on a fitted design does not by itself justify predictions for sequences outside its row space.

## Context

Graduate level (statistical identifiability in biophysical models). The point reconciles disagreements among published NN parameter sets: sets that look different can make identical polymer predictions. The same identifiability question arises whenever additive energy models are fitted to aggregate measurements, including models used to design hybridizing strands.

## Depends on

- [Nearest-neighbor model of DNA duplex stability](nearest-neighbor-model-of-duplex-stability.md)

## Proof depends on

None.

## Expansion

Proof of item 1: in a cyclic word every occurrence of a base is followed by exactly one base and preceded by exactly one base, so for each base $a$ the number of dinucleotides starting with $a$ equals the number ending with $a$, which is Eq. 6 (and Eq. 9 for $a=A$ and $a=G$). Derived equivalent in the ten doublet classes (our own derivation, not printed in the cited sources): assign to each base a value $g$ with $g(\bar a)=-g(a)$ for its complement $\bar a$, and sum $g(a)-g(b)$ over all doublets $ab$ around the cycle of the top strand; the sum telescopes to zero. A doublet and its reverse complement $\bar b\bar a$ contribute $g(\bar b)-g(\bar a)=g(a)-g(b)$, the same amount, so the sum is a function of the ten doublet counts. The two independent choices $g=(A,C,G,T)\mapsto(1,0,0,-1)$ and $(0,1,-1,0)$ give

$$2v_{AT/TA}-2v_{TA/AT}-v_{CA/GT}+v_{GT/CA}+v_{CT/GA}-v_{GA/CT}=0,\qquad v_{CA/GT}-v_{GT/CA}+v_{CT/GA}-v_{GA/CT}+2v_{CG/GC}-2v_{GC/CG}=0$$

for the doublet-count vector $v$ (up to sign and scaling). Their independence is visible in the $AT/TA$ and $CG/GC$ components. Item 2 is linear algebra. Item 3: the null vectors have zero $AA/TT$ and $GG/CC$ entries, so those coordinates of $p$ are constant on $p_0+\ker S$ when $\ker S$ is exactly the span of the two relations (rank $8$). Numerical check: for several hundred random cyclic sequences the count matrix has rank exactly $8$ and both vectors are in its kernel; random linear sequences give rank $10$, and $12$ with two initiation columns.

Remaining decomposition before the page can be marked ready: (i) the telescoping identity as a lemma on cyclic words; (ii) an explicit rank-$8$ design with its count matrix (for example the eight sequences quoted by the source, whose list is rendered as an image in the copy read); (iii) a definition page for the doublet-count map shared with the NN model page.

## Sources

- J. SantaLucia Jr., "A unified view of polymer, dumbbell, and oligonucleotide DNA nearest-neighbor thermodynamics", *Proceedings of the National Academy of Sciences USA* 95(4) (1998), 1460–1465, [doi.org](https://doi.org/10.1073/pnas.95.4.1460); open-access copy read: [pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC19045/), Methods, subsection "The Rank of the Stacking Matrix" (column rank and invariants; eight invariants for polymers because of NN composition constraints; nine for dumbbells; full parameter sets for oligonucleotides; non-uniqueness of least-squares NN parameters and the SVD solution; uniqueness of AA/TT and GG/CC), including "A convenient set of eight linearly independent sequences was provided by Vologodskii *et al.* (10)" (the set itself is rendered as an image).
- P. Licinio and J. C. O. Guerra, "Irreducible representation for nucleotide sequence physical properties and self-consistency of nearest-neighbor dimer sets", *Biophysical Journal* 92(6) (2007), 2000–2006, [doi.org](https://doi.org/10.1529/biophysj.106.095059); open-access copy read: [pmc.ncbi.nlm.nih.gov](https://pmc.ncbi.nlm.nih.gov/articles/PMC1861801/), Eq. 6 (the four single-strand closure relations for circular sequences, of which "any three" are taken; equation image viewed) and section "Double strands", Eq. 9 (the two independent double-strand relations, equation image viewed) and the surrounding text: "only 10 conjugated NN dimer pair values ... linked through two independent composition closure relations ... so that only eight independent parameters should result".
