# Carroll (Desnanot–Jacobi) identity

Let $R$ be a commutative ring, let $n$ be a natural
number, and let $C$ be an $(n + 2) \times (n + 2)$ matrix over $R$. For indices $a$ and $b$,
write $C^{a}_{b}$ for the $(n + 1) \times (n + 1)$ matrix obtained from $C$ by deleting row $a$
and column $b$. Let $i \ne j$ be distinct indices and let $C^{ij}_{ij}$ be the $n \times n$
matrix obtained from $C$ by deleting rows $i$ and $j$ and columns $i$ and $j$. Then

$$\det C \cdot \det C^{ij}_{ij} = \det C^{i}_{i} \det C^{j}_{j} - \det C^{i}_{j} \det C^{j}_{i}.$$

For $n = 0$ the matrix $C^{ij}_{ij}$ is empty and its determinant is $1$.

## Sources

- Charles Delorme and Guillermo Pineda-Villavicencio, "Quadratic Form Representations via Generalized Continuants", Journal of Integer Sequences 18 (2015), Article 15.6.4, displayed lemma lines 133–142. Stable source URL: https://cs.uwaterloo.ca/journals/JIS/VOL18/Pineda/pin2.tex Verified source-file SHA-256: `ce4b0fb99a549cee767baa4defe39148a2cfa410e48b8919e20efcecb26a7169`. Verified normalized no-final-newline span SHA-256: `26bf5c11571feef0d9bbd84618b3819749cd8e8e2bd83239b235cdc627030542`. The source cites C. L. Dodgson, "Condensation of determinants, being a new and brief method for computing their arithmetical values", Proc. Roy. Soc. Lond. 15 (1866), 150–155. Proves `Wanted` entry `carroll_identity`.
