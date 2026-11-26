# Mean absorption time of the Wright–Fisher diffusion with selection

For real numbers $\sigma$ and $p$, let

$$T_\sigma(p) = \int_0^1 \Psi_\sigma(p, x)\, dx,$$

where $\Psi_\sigma$ is the [sojourn density of the diffusion with selection](../allele-age-and-the-maruyama-effect/selection-green.md) and the
integral of a function that is not integrable on $[0, 1]$ is taken to be $0$. For $p \in [0, 1]$,
$T_\sigma(p)$ is the mean time until absorption, by loss or fixation, of an allele at initial
frequency $p$ in the Wright–Fisher diffusion with genic selection $\sigma = 2Ns$ and no mutation,
in units of $2N$ generations. For $p < 0$ or $p > 1$ the integrand is not integrable (it behaves
like a nonzero multiple of $1/x$ near $x = 0$, respectively of $1/(1 - x)$ near $x = 1$), so
$T_\sigma(p) = 0$ there.

## Sources

- M. Kimura and T. Ohta, *The average number of generations until fixation of a mutant gene in a
  finite population*, Genetics 61 (1969), 763–771.
- W. J. Ewens, *Mathematical Population Genetics I: Theoretical Introduction*, 2nd ed., Springer
  (2004), §5.3.
