# All death-Birth amplifiers are bounded

Fix $r > 1$. For every population structure $G_N$ on $N$ vertices (edges possibly directed and
weighted, no self-loops), the fixation probability of a single mutant of fitness $r$ placed
uniformly at random under death-Birth updating satisfies

$$\rho_{\mathrm{dB}}(G_N, r) \ \le\ 1 - \frac{1}{r+1}.$$

Consequently, for a family $\{G_N\}_{N \ge 1}$ whose implied scale of fitness
$\mathrm{isf}(r)$ is defined by
$\liminf_{N \to \infty} \rho_{\mathrm{dB}}(G_N, r) = 1 - 1/\mathrm{isf}(r)$, one has
$\mathrm{isf}(r) \le r + 1$ for all $r > 1$: under death-Birth updating there are no linear
amplifiers with $\mathrm{isf}(r) \ge c_1 r + c_0$ for a constant $c_1 > 1$, hence no quadratic
amplifiers and no super amplifiers (families with $\mathrm{isf}(r) = \infty$, i.e. guaranteed
fixation in the large-population limit).

## Depends on

- [Fixation bound from the average out-degree](fixation-bound-from-average-out-degree.md)

## Proof sketch

The bound of the previous article, $d r/(dr + d + r - 1)$, is increasing in the average out-degree
$d$ and tends to $r/(r+1) = 1 - 1/(r+1)$ as $d \to \infty$, so the limiting value is an upper bound
for every $d$. This is in sharp contrast with Birth-death updating, where the star graph already
rescales fitness from $r$ to $r^2$ and super amplifiers exist.

## Sources

- J. Tkadlec, A. Pavlogiannis, K. Chatterjee, M. A. Nowak, "Limits on amplifiers of natural selection under
  death-Birth updating", PLoS Computational Biology 16 (2020) e1007494, Theorem 2,
  <https://doi.org/10.1371/journal.pcbi.1007494> (PMC6968837).
