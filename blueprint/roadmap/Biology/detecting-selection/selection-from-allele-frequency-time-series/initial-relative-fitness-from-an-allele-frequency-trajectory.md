# Initial relative fitness from an allele-frequency trajectory

**Model.** In an asexual population let a lineage carrying a focal mutation have Malthusian fitness exceeding the population mean by a constant $s$ while it is rare enough not to move the mean. Then its frequency $f(t)$ obeys the logistic equation $\dot f = s f(1-f)$, so the logit is linear in time:

$$\ln\frac{f(t)}{1-f(t)} = \ln\frac{f(t_1)}{1-f(t_1)} + s\,(t - t_1).$$

**Estimator.** Given frequencies at two times $t_1 < t_2$ with $0 < f(t_1), f(t_2) < 1$,

$$s_{\mathrm{up}} = \frac{1}{t_2 - t_1}\left(\ln\frac{f(t_2)}{1-f(t_2)} - \ln\frac{f(t_1)}{1-f(t_1)}\right),$$

with time measured in generations. Taking $t_1 < t_2$ to be the first pair of consecutive sampling times with $f(t_1) > 0$ and $f(t_2) > 0.1$ gives the initial relative fitness.

**Interpretation.** $s_{\mathrm{up}}$ estimates the fitness of the whole genetic background carrying the mutation relative to the current population mean, not the mutation's own effect: a neutral mutation arising on a background $3\%$ fitter than average and a mutation conferring $3\%$ on a neutral background give the same value. Because the mean fitness rises as other lineages sweep, $s_{\mathrm{up}}$ is only a local, early-time quantity.

## Expansion

Writing $x = f/(1-f)$ for the odds of the lineage, $\dot x = s x$ under the logistic dynamics, so $\ln x$ increases linearly at rate $s$ and the two-point difference quotient is its natural estimator. In 40 evolving yeast populations sequenced at about 80-generation intervals, the fixation probability of a mutation increased with $s_{\mathrm{up}}$, and nonsynonymous mutations, especially those in genes hit in several replicate populations, had higher $s_{\mathrm{up}}$ than synonymous ones, as expected if those classes carry larger advantages.

## Sources

- G. I. Lang, D. P. Rice, M. J. Hickman, E. Sodergren, G. M. Weinstock, D. Botstein, M. M. Desai, "Pervasive genetic hitchhiking and clonal interference in forty evolving yeast populations", Nature (2013), Methods ("Estimating the initial relative fitness of mutations"), <https://doi.org/10.1038/nature12344>.
