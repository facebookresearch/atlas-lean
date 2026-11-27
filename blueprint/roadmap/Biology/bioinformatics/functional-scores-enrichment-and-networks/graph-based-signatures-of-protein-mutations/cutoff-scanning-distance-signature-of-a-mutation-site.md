# Cutoff-scanning distance signature of a mutation site

Let a protein structure be given, together with a point mutation of residue $r$ from the wild-type
amino acid to a mutant amino acid. Let $L$ be a finite set of atom classes and $\ell$ a labelling that
assigns a class to each atom. The source uses three classifications: a single class; polar versus
hydrophobic; and eight pharmacophore classes (hydrophobic, positive, negative, hydrogen acceptor,
hydrogen donor, aromatic, sulphur, neutral).

1. **Environment.** Let $A$ be the set of atoms within distance $\rho$ of the geometric centre of the
   wild-type residue $r$, and let $d(x, y)$ be the Euclidean distance between atoms $x, y \in A$.
2. **Contact graphs.** For a cutoff $\delta > 0$, let $G_\delta$ be the graph on $A$ with an edge
   between $x \ne y$ when $d(x, y) \le \delta$.
3. **Cutoff scan.** For cutoffs $\delta = D_{\min}, D_{\min} + D_{\mathrm{step}}, \dots, D_{\max}$ and
   for each unordered pair of classes $\{u, v\} \subseteq L$, record the number of edges of $G_\delta$
   joining an atom of class $u$ to an atom of class $v$,

$$c_{\{u,v\}}(\delta) = \#\bigl\{\{x, y\} \subseteq A : x \ne y,\ d(x, y) \le \delta,\
\{\ell(x), \ell(y)\} = \{u, v\}\bigr\}.$$

   As a function of $\delta$ this is the cumulative distribution of interatomic distances by class pair.
4. **Pharmacophore change.** Let $p^{\mathrm{wt}}, p^{\mathrm{mt}} \in \mathbb{N}^{L}$ count the atoms of
   each class in the wild-type and mutant side chains, and append
   $p^{\mathrm{change}} = p^{\mathrm{mt}} - p^{\mathrm{wt}}$.

The signature of the mutation is the concatenation of all $c_{\{u,v\}}(\delta)$, the vector
$p^{\mathrm{change}}$ and, when available, experimental conditions (pH, temperature) and the relative
solvent accessibility of the residue. It is used as the feature vector of supervised regression or
classification models of the change in folding free energy or binding affinity.

## Remarks

Scanning the cutoff encodes the whole distance matrix of the environment in a fixed-length vector,
covering short-range contacts such as hydrogen bonds and long-range packing, without choosing one
contact threshold. Only the wild-type structure is used, so no mutant model is needed. The change in
residue character and size enters through $p^{\mathrm{change}}$, and its effect is learned from data
rather than imposed through penalties for burying polar or exposing hydrophobic groups. Burial and
residue depth are captured implicitly, because a buried residue has many more edges at every cutoff.

## Sources

- D. E. Pires, D. B. Ascher, T. L. Blundell, "mCSM: predicting the effects of mutations in
  proteins using graph-based signatures", Bioinformatics 30 (2014) 335-342, Section 2.1, "mCSM:
  graph-based signatures", and Algorithm 1, <https://doi.org/10.1093/bioinformatics/btt691>
  (PMC3904523).
