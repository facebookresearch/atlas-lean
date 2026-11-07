# r-Stirling numbers of the second kind

For natural numbers $n$, $m$ and $r$, Broder's
r-Stirling number of the second kind ${n \brace m}_r$ is $0$ unless $r \le m$ and $r \le n$, and
otherwise

$${n \brace m}_r = \sum_{i=0}^{n-r} \binom{n-r}{i} {n-r-i \brace m-r} r^i,$$

where ${a \brace b}$ denotes the Stirling number of the second kind (and $0^0 = 1$).

## Sources

- A. Z. Broder, *The r-Stirling numbers*, Discrete Mathematics 49 (1984), 241-259; Kunle Adegoke and Robert Frontczak, *Three Classes of Combinatorial Sums Involving Central Binomial Coefficients and Harmonic Numbers*, INTEGERS 26 (2026), Article A109, Section 4 (exponential generating function of `{m+v \brace k+v}_v`).
