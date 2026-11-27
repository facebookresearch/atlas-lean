# Pseudocount emission estimate of a match state

For a finite alphabet, the residues $c$ that a multiple alignment places in a column (gaps omitted), pseudocounts $\beta(a)$ in a field and a residue $a$, the estimate is

$$\hat e(a) = \frac{n_a + \beta(a)}{|c| + \sum_b \beta(b)},$$

where $n_a$ is the number of occurrences of $a$ in $c$, with the convention $x/0 = 0$. Laplace's rule is $\beta \equiv 1$ (Durbin et al. 1998).

## Sources

- R. Durbin, S. R. Eddy, A. Krogh and G. Mitchison, *Biological Sequence Analysis: Probabilistic Models of Proteins and Nucleic Acids*, Cambridge University Press (1998).
