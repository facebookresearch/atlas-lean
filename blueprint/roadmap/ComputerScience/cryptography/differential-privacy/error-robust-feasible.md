# β-feasible word

For a real number $\beta$, a word $w$ of length $d$ is $\beta$-feasible
for the coalition $S$ of the codebook $C$, $w \in F_\beta(C_S)$, when
$(1 - \beta)\, d \le \#\{j : \exists i \in S,\ w_j = c_{ij}\}$: at least a $1 - \beta$ fraction of
its columns are feasible. For $d > 0$ this is the condition
$\Pr_{j \leftarrow [d]}[\exists i \in S,\ w_j = c_{ij}] \ge 1 - \beta$ multiplied by $d$, which the
source states for $\beta \in [0, 1]$; every word is $\beta$-feasible when $d = 0$ or $\beta \ge 1$.

## Sources

- M. Bun, J. Ullman and S. Vadhan, *Fingerprinting codes and the price of approximate differential privacy*, SIAM J. Comput. 47(5), 2018, arXiv:1311.3158v3, Section 3.1.
