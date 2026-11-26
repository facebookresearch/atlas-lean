# Higher moments of allele age and comparison with first arrival

For a neutral allele segregating at frequency $x$ in a population of effective size $N_e$, Kimura and Ohta (1973, abstract) obtain by the diffusion method, for $4N_ev < 1$ with $v$ the mutation rate and assuming the allele has drifted up from a very low frequency, formulas for the mean and the mean square of its age; for current frequency $10\%$ the expected age is roughly $N_e$ generations with standard deviation $1.4N_e$. They also give formulas for the mean first-arrival time of a neutral mutant at frequency $x$. The mean age is $-4N_ex\log x/(1 - x)$ generations, which at $x = 0.1$ equals $(0.4\log 10/0.9)N_e \approx 1.02N_e$, in agreement with the stated example. The second and higher moments of age are moments of an additive path functional along the conditioned path: Maruyama and Kimura (1975, abstract) compute any moment of the sum of a function of gene frequency along sample paths between two specified frequencies, and Nagylaki (1974, abstract) derives a formula, in terms of sojourn times, for the moments of the integral of an arbitrary function of gene frequency along sample paths, for conditioned and unconditioned processes.

## Depends on

- [Mean age of a neutral allele](../../../../Biology/population-genetics/diffusion-theory/allele-age-and-the-maruyama-effect/mean-age-zero.md)
- [Mean age as the limit of conditional sojourn times](../../../../Biology/population-genetics/diffusion-theory/allele-age-and-the-maruyama-effect/tendsto-integral-age-density.md)
- [Moment recursion for additive path functionals](../../../../Probability/stochastic-calculus/one-dimensional-diffusions/kac-maruyama-kimura-moment-recursion.md)

## Expansion

1. The second moment of the age of a neutral allele at frequency $x$ in the rare-origin limit, from the moment recursion applied along the conditioned path.
2. The variance and the numerical example at $x = 0.1$ (standard deviation about $1.4N_e$ generations).
3. The mean first-arrival time at $x$ of a new neutral mutant conditioned to reach $x$, and its comparison with the mean age at the same frequency.
4. The relation between the two laws: an allele observed at $x$ is selected with weight proportional to the time its path spends at $x$, as a separate statement.

## Sources

- M. Kimura and T. Ohta, The age of a neutral mutant persisting in a finite population, Genetics 75 (1973), 199–212, abstract. <https://doi.org/10.1093/genetics/75.1.199>
- T. Maruyama and M. Kimura, Moments for sum of an arbitrary function of gene frequency along a stochastic path of gene frequency change, Proc. Natl. Acad. Sci. USA 72 (1975), 1602–1604, abstract. <https://doi.org/10.1073/pnas.72.4.1602>
- T. Nagylaki, The moments of stochastic integrals and the distribution of sojourn times, Proc. Natl. Acad. Sci. USA 71 (1974), 746–749, abstract. <https://doi.org/10.1073/pnas.71.3.746>
