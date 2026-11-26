# Replace-one adjacency

Two databases $d, d' : \mathrm{Fin}\,n \to X$ with $n$ rows over a row type $X$ are *replace-one adjacent* when the set of indices on which they differ,

$$
\{\, i \mid d(i) \ne d'(i) \,\},
$$

has at most one element. Equal databases are adjacent, including the empty database when $n = 0$, so the relation is the reflexive closure of "differ in exactly one row".

## Sources

- C. Dwork, F. McSherry, K. Nissim and A. Smith, *Calibrating Noise to Sensitivity in Private Data Analysis*, TCC 2006, Section 2, Definition 1, <https://people.csail.mit.edu/asmith/PS/sensitivity-tcc-final.pdf> (neighbours differing in one entry).
