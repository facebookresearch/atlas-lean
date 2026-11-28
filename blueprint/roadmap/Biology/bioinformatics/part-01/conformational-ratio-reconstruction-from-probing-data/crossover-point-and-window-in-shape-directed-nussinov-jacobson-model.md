# Crossover point and window in the SHAPE-directed Nussinov–Jacobson model

**Model.** For an RNA structure $A$ of length $n$ and auxiliary probing data $M\in[0,1]^n$, the SHAPE-directed Nussinov–Jacobson pseudoenergy is

$$
E(A\mid M)=-\mathrm{bp}(A)+C\sum_{i=1}^n|x_i-M_i|,
$$

where $\mathrm{bp}(A)$ counts paired nucleotides, $x_i=1$ if nucleotide $i$ is unpaired in $A$ and $0$ otherwise, and $C>0$ weights the data. Structures are Boltzmann distributed, $\mathbb{P}(A\mid M)\propto e^{-E(A\mid M)/RT}$. For two structures $A,B$ with noiseless binary data $S_i,T_i$ (1 = unpaired), the mixed data of a ratio $p$ of $A$ is $M(p)=pS+(1-p)T$. Let $\mathrm{bp}(A-B)$ count nucleotides paired in $A$ but not in $B$ and $\mathrm{bp}(A\Delta B)$ those paired in exactly one of them. The *crossover point* is the $p$ at which $A$ and $B$ are predicted equally likely; the *crossover window* is the set of $p$ at which both are predicted with probability at least $0.1$.

**Lemma (crossover point).**

$$
p^*=\frac12+\frac{1}{2C}-\frac{\mathrm{bp}(A-B)}{C\,\mathrm{bp}(A\Delta B)}.
$$

**Lemma (crossover window).** The crossover window has length at most $\dfrac{RT\ln9}{C\,\mathrm{bp}(A\Delta B)}$.

**Theorem (asymptotic non-reconstructibility).** Fix $q\in(0,1)$ and $C>0$, and draw pairs of length-$n$ structures with each nucleotide paired independently with probability $q$. Let $P_n$ be the probability that some conformational ratio cannot be reconstructed by the model with total variation distance below $0.25$. Then $P_n\to1$ as $n\to\infty$.

## Expansion

Only nucleotides whose pairing status differs contribute to the data term, so $E(A\mid M(p))$ is affine in $p$ with slope proportional to $C\,\mathrm{bp}(A\Delta B)$, and equating the energies of $A$ and $B$ gives $p^*$. Requiring both odds ratios $\mathbb{P}(A)/\mathbb{P}(B)$ and its inverse to be at least $1/9$ confines the energy difference to an interval of width $RT\ln9$, hence the window bound. For random structures $\mathrm{bp}(A\Delta B)$ grows linearly in $n$ while $\mathrm{bp}(A-B)-\mathrm{bp}(B-A)$ fluctuates on the scale $\sqrt n$: either the window shrinks (large $C$) or the crossover point drifts away from $1/2$ (small $C$), and no single $C$ avoids both, which is the theorem. The trade-off explains why pseudoenergy methods collapse bimodal ensembles onto one structure.

## Depends on

- [RNA secondary structure](../../nussinov-algorithm-for-rna-secondary-structure/is-structure.md)

## Sources

- Torin Greenwood, Christine E. Heitsch, "Deconvolving RNA Base Pairing Signals", arXiv:1801.03055: Section 4 (pseudoenergy models with noiseless auxiliary data): Theorem 1, Lemma 2 (crossover point), Lemma 3 (crossover window). <https://doi.org/10.48550/arXiv.1801.03055>
