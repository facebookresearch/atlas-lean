# Purging of recessive mutation burden after a bottleneck

Keep the model and notation of the [mutation burden and burden ratio](mutation-burden-and-the-burden-ratio.md), now with fully recessive alleles ($h = 0$): only derived homozygotes lose fitness $s$.

**Equilibrium.** For $h=0$ the equilibrium spectrum is

$$\phi^{R}_0(x) = \frac{\theta_0\, e^{-2N_0 s x^2}}{x(1-x)}\left[1-\frac{\int_0^x e^{2N_0 s y^2}\,dy}{\int_0^1 e^{2N_0 s y^2}\,dy}\right], \qquad \theta_0 = 4N_0U_d,$$

which decays more slowly than the additive spectrum at low frequency (alleles hide in heterozygotes) and faster, like $e^{-2N_0 s x^2}$, at high frequency. When $2N_0 s \gg 1$ the bracket is close to $1$ wherever the factor $e^{-2N_0 s x^2}$ is not negligible, and the burden is approximately

$$\langle x\rangle_0 \approx \theta_0 \int_0^\infty e^{-2N_0 s x^2}\,dx = U_d\sqrt{\frac{2\pi N_0}{s}},$$

of order $U_d\sqrt{N_0/s}$, much larger than the additive burden $2U_d/s$.

**Moment equation.** For recessive selection the first moment obeys, after dropping a selection term in $\langle x^3\rangle$ of order $O(1/\sqrt{N_0 s})$ (the order the source states after its Eq. (13)),

$$\partial_t \langle x\rangle \approx U_d - s\,\langle x^2\rangle,$$

so the burden is driven by the *second* moment, the variance of the spectrum, rather than by the burden itself.

**Effect of a bottleneck.** Model a single-generation bottleneck to $N_B$ individuals as binomial sampling of $2N_B$ chromosomes: an allele at frequency $y$ is carried by $k$ copies with probability $\binom{2N_B}{k}y^k(1-y)^{2N_B-k}$. Sampling preserves the expected frequency but raises its second moment,

$$\mathbb{E}\Bigl[\tfrac{k}{2N_B}\Bigr] = y, \qquad \mathbb{E}\Bigl[\bigl(\tfrac{k}{2N_B}\bigr)^2\Bigr] = y^2 + \frac{y(1-y)}{2N_B},$$

so immediately after re-expansion $\langle x\rangle$ is unchanged while $\langle x^2\rangle$ has grown by $\bigl(\langle x\rangle - \langle x^2\rangle\bigr)/(2N_B)$. By the moment equation, purging accelerates: derived homozygotes created by drift are removed, the burden falls below its equilibrium value, reaches a minimum on a time scale set by selection (short compared with the drift time $2N_0$), and then slowly recovers as new mutations drift up. In the strong-selection, low-intensity regime $2N_B > \sqrt{2N_0 s} > 1$ (equivalently, a bottleneck with $N_B \gg \sqrt{N_0 s}$ under strong selection $2N_0 s \gg 1$) this gives

$$B_R(t_{\min}) > 1,$$

with an explicit expansion in the source (Eqs. (15)–(19)); for short bottlenecks the single-generation result extends by replacing $(2N_B)^{-1}$ with the intensity $I_B = T_B/(2N_B)$, and simulations show the approximation holds for $I_B \lesssim 1/10$.

**Signature.** Additive alleles give $B_R \le 1$ after a bottleneck, recessive alleles give $B_R > 1$; a burden ratio above $1$ in a gene set compared between a bottlenecked and a non-bottlenecked population therefore indicates predominantly recessive selection.

## Depends on

- [Mutation burden, the burden ratio and the additive response to a bottleneck](mutation-burden-and-the-burden-ratio.md)
- [Mutation–selection balance for a recessive allele](../recessive-mutation-selection-balance.md)
- [Variance of a binomial random variable](../../../../Probability/distributions/discrete/binomial-distribution/variance-of-has-law-binomial.md)

## Expansion

The recessive selection term per site is $-s\,x^2(1-x)$ to leading order, so summing over sites gives $-s(\langle x^2\rangle - \langle x^3\rangle)$, and the cubic moment is subdominant under strong selection. The binomial moment identities are the mean and variance of a binomial count. The key contrast with the additive case is that the additive equation involves $\langle x\rangle$ itself, which a sampling event does not change, while the recessive equation involves $\langle x^2\rangle$, which a sampling event always raises. A bottleneck therefore exposes recessive alleles in homozygous form and removes them faster than new mutations replace them, and the temporary deficit is what the burden ratio detects.

## Sources

- D. J. Balick, R. Do, C. A. Cassa, D. Reich and S. R. Sunyaev, "Dominance of deleterious alleles controls the response to a population bottleneck", PLoS Genetics (2015), Results, Eqs. (11)–(19) and "Extended population bottlenecks", <https://doi.org/10.1371/journal.pgen.1005436>, PMCID PMC4552954.
- M. Kirkpatrick and P. Jarne, "The effects of a bottleneck on inbreeding depression and the genetic load", The American Naturalist (2000) (qualitative prediction that recessive load is purged after a bottleneck; background).
