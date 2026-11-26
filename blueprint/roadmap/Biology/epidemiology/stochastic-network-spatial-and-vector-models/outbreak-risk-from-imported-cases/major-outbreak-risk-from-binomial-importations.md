# Risk of a major outbreak from binomially many imported cases

**Setting.** A source region has accumulated $C \in \mathbb{N}$ infected individuals. Each of them, independently, ends up mixing into the population of a destination country with probability $\theta \in [0,1]$ (the *connectivity*: the baseline probability of travelling to that destination, multiplied by the fractions not stopped by travel reduction, exit screening and entry screening). The number of imported cases is therefore

$$X \sim \mathrm{Bin}(C, \theta).$$

Each imported case independently starts a Galton–Watson branching process whose offspring law is negative binomial with mean $R_{\mathrm{loc}} > 0$ (the local reproduction number) and dispersion $k > 0$, with probability generating function

$$g(s) = \Big(1 + \frac{R_{\mathrm{loc}}}{k}(1 - s)\Big)^{-k}, \qquad s \in [0,1].$$

Let $z \in [0,1]$ be the extinction probability of one such branch, i.e. the least root of $z = g(z)$ in $[0,1]$; $z < 1$ exactly when $R_{\mathrm{loc}} > 1$.

**Statement.** Conditional on $X = i$, the outbreak dies out iff all $i$ independent branches die out, so the probability of a major outbreak is $1 - z^i$. The unconditional risk is

$$\mathrm{Risk}(C, \theta, R_{\mathrm{loc}}) = \mathbb{E}\big[1 - z^{X}\big] = 1 - \big(1 - \theta(1 - z)\big)^{C}.$$

Consequences:

- $\mathrm{Risk} = 0$ whenever $R_{\mathrm{loc}} \le 1$ (then $z = 1$), and also when $\theta = 0$ or $C = 0$.
- For $R_{\mathrm{loc}} > 1$ the risk is strictly increasing in $C$ when $\theta > 0$, strictly increasing in $\theta$ when $C \ge 1$, and tends to $1$ as $C \to \infty$ with $\theta > 0$ fixed.
- The risk depends on $C$ and $\theta$ only through the per-case escape probability $\theta(1 - z)$, and for small $\theta(1-z)$ and large $C$ it is approximately $1 - e^{-C\theta(1 - z)}$: halving the connectivity has the same effect as halving the cumulative case count at the source.
- Since $z$ decreases as $R_{\mathrm{loc}}$ increases and increases as $k$ decreases (stronger superspreading), lowering the local reproduction number and lowering connectivity are two separate levers acting on the same exponent.

## Depends on

- [Negative-binomial offspring distribution](../../superspreading-and-negative-binomial-offspring/nb-offspring.md)
- [Negative-binomial extinction probability is the least fixed point](../../superspreading-and-negative-binomial-offspring/is-least-extinction-prob-nb-offspring.md)
- [Superspreading raises the extinction probability](../../superspreading-and-negative-binomial-offspring/extinction-prob-nb-offspring-antitone.md)

## Expansion

The closed form is the probability generating function of the binomial law evaluated at $z$: $\mathbb{E}[z^X] = \sum_{i=0}^{C} \binom{C}{i} \theta^i (1-\theta)^{C-i} z^i = (1 - \theta + \theta z)^C$. Independence of branches gives $\Pr(\text{all } i \text{ branches go extinct}) = z^i$. Monotonicity in $C$ and $\theta$ is immediate because $0 \le 1 - \theta(1 - z) \le 1$. The approximation uses $\log(1 - x) \approx -x$. In the source study the connectivity was assembled multiplicatively from a travel-network importation probability and screening efficacies, and the offspring dispersion was taken as $k = 0.64$; the analysis then maps risk over $(\theta, R_{\mathrm{loc}})$, showing that poorly connected countries with high $R_{\mathrm{loc}}$ gain most from reducing importations, while well-connected countries gain most from reducing $R_{\mathrm{loc}}$.

## Sources

- P. Boldog, T. Tekeli, Z. Vizi, A. Dénes, F. A. Bartha, G. Röst, "Risk assessment of novel coronavirus COVID-19 outbreaks outside China", Journal of Clinical Medicine (2020), Sections 2.3–2.5 (connectivity, binomial importation, Galton–Watson risk $\mathrm{Risk}_x = E[1 - z^X]$), <https://doi.org/10.3390/jcm9020571> (PMC7073711).
