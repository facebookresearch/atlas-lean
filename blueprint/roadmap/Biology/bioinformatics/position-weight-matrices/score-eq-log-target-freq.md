# Every such score matrix is a log-odds matrix

If $p_a > 0$ for every $a$ and $\lambda > 0$, then for every score matrix $s$ and all $a, b$,

$$s_{ab} = \frac{1}{\lambda} \log \frac{q_{ab}}{p_a p_b},$$

where $q$ are the [target frequencies](target-freq.md) (Karlin and Altschul 1990).

## Sources

- S. Karlin and S. F. Altschul, *Methods for assessing the statistical significance of molecular sequence features by using general scoring schemes*, PNAS 87 (1990), 2264–2268.
