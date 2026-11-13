# Block lengths of the higher-order Gijswijt sequences

For a natural number $m$, write
$A^{(m)}(k)$ for the $k$th term of the $m$th order sequence. The block lengths $\beta^{(m)}(t)$
are defined by $\beta^{(m)}(0) = 0$, $\beta^{(m)}(1) = 1$ and, for $t \ge 1$, $\beta^{(m)}(t+1)$
is the least $k > (m+1)\,\beta^{(m)}(t)$ with $A^{(m)}(k+1) = m$, or $0$ if there is no such $k$.

This matches the paper's recursion $B_{t+1} = (B_t)^{m+1} S_t$ for the blocks $B_t$: the glue
string $S_t$ is the run of terms after position $(m+1)\,\beta^{(m)}(t)$ up to the next $m$.

## Sources

- Levi van de Pol, *The Growth Rate of Gijswijt's Sequence*, Journal of Integer Sequences 28 (2025), Article 25.4.6, Section 2 (blocks `B_t^{(m)}`, glue strings `S_t^{(m)}`, and their lengths `β^{(m)}(t)`).
