# The log-odds score is a log-likelihood ratio

If $p_i(b) > 0$ and $q(b) > 0$ for all $i, b$, then for every site $s$

$$\mathrm{sc}_{L}(s) = \log \frac{\prod_i p_i(s_i)}{\prod_i q(s_i)},$$

where $L$ is the [log-odds matrix](log-odds.md) and $\mathrm{sc}$ the [score](score.md) (Staden 1989; Stormo 2000).

## Sources

- R. Staden, *Methods for calculating the probabilities of finding patterns in sequences*, CABIOS 5 (1989), 89–96.
- G. D. Stormo, *DNA binding sites: representation and discovery*, Bioinformatics 16 (2000), 16–23.
