# Process interpretation of allele age via time reversal

This node covers a research target for the Wright–Fisher diffusion without mutation ($\theta = 0$): to identify Maruyama's density for the age of an allele observed at frequency $x$ with the expected occupation density of the time-reversed process, namely the frequency path of an allele traced back to its origin at frequency $0+$. The analytic formulas for the [mean age of an allele at a given frequency](mean-age.md) are stated separately; the target here is the process-level identity behind them.

## Expansion

A good expansion splits this target into separately stated results, each with its hypotheses fixed from a source, and proves them from the prerequisites below:

- the reversed frequency process of a new allele, defined by an entrance law from $0+$ and a Doob $h$-transform;
- the identification of the age density with the expected occupation density of that reversed process;
- in the neutral case, the reduction to an explicit reversed neutral process.

Prerequisites:

- [Mean age of an allele at a given frequency](mean-age.md)
- [Doob h-transform: process conditioned on fixation](../fixation-and-absorption-in-the-wright-fisher-dif/doob-h-transform-process-conditioned-on-fixation.md)
- [Occupation-time formula and mean absorption time with selection](../sojourn-times-of-the-wright-fisher-diffusion/occupation-time-formula-and-mean-absorption-time.md)

## Sources

- T. Maruyama, "The age of an allele in a finite population", *Genetical Research* 23:137–143, 1974, <https://resolve.cambridge.org/core/services/aop-cambridge-core/content/view/0A1A0C7B0C0C7CD473544FD3C5F1B01A/S0016672300014750a.pdf/age_of_an_allele_in_a_finite_population.pdf> (reversibility argument)
- W. J. Ewens, *Mathematical Population Genetics I: Theoretical Introduction*, 2nd ed., Springer, 2004, Chapter 4, <https://doi.org/10.1007/978-0-387-21822-9> (background)
