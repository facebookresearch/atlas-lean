# Transmission-based false discovery rate for de novo mutations

Suppose $y \ge 1$ putative de novo mutations (DNMs) are called in an individual of generation F1, of which an unknown number $w \in \{0, 1, \dots, y\}$ are real. Assume that each real DNM is independently observed in a given F2 offspring with known probability $q \in (0, 1)$ (about $1/2$, adjusted for detection power), and that false calls are never observed in the F2. Then the number $z$ of putative DNMs observed in the F2 satisfies

$$z \mid w \sim \mathrm{Binomial}(w, q),$$

and the per-trio false discovery rate is estimated by $\widehat{\mathrm{FDR}} = 1 - \hat w / y$, where $\hat w$ maximizes the likelihood over integers $z \le w \le y$.

**Proposition (closed form).** If $z \ge 1$, the likelihood $L(w) = \binom{w}{z} q^z (1-q)^{w-z}$ satisfies, for $w > z$,

$$\frac{L(w)}{L(w - 1)} = \frac{w (1 - q)}{w - z},$$

which is $\ge 1$ iff $w \le z/q$. Hence $L$ increases up to $\lfloor z/q \rfloor$ and decreases after it, and the constrained maximum likelihood estimate is

$$\hat w = \min\big(y, \lfloor z / q \rfloor\big)$$

(when $z/q$ is an integer not exceeding $y$, both $z/q$ and $z/q - 1$ are maximizers). If $z = 0$ then $\hat w = 0$. In particular $\widehat{\mathrm{FDR}} = \max\big(0, 1 - \lfloor z/q \rfloor / y\big)$.

With two F2 siblings and independent transmissions to each, the four observation patterns (seen in neither, first only, second only, both) are multinomial with probabilities $\big((1-q_1)(1-q_2), q_1(1-q_2), (1-q_1)q_2, q_1q_2\big)$ given $w$.

## Expansion

The ratio follows from $\binom{w}{z} / \binom{w-1}{z} = w/(w - z)$. Since $z/q \ge z$, the unimodal likelihood restricted to $[z, y]$ peaks at $\min(y, \lfloor z/q \rfloor)$. For $z = 0$, $L(w) = (1 - q)^w$ is decreasing. Wu et al. take $q$ from simulated DNMs passed through the same pipeline, rather than exactly $1/2$, because detection power is below one and joint calling up-weights variants seen several times; for one human trio, $44$ of $89$ DNMs were seen in the offspring against an expected $89 \times 0.492 \approx 44$, giving $\widehat{\mathrm{FDR}} \approx 0$, consistent with Sanger validation.

## Sources

- F. L. Wu, A. I. Strand, L. A. Cox, C. Ober, J. D. Wall, P. Moorjani and M. Przeworski, "A comparison of humans and baboons suggests germline mutation rates do not track cell divisions", PLoS Biology 18 (2020), e3000838, Methods "Estimating FDRs", <https://doi.org/10.1371/journal.pbio.3000838>, PMCID PMC7467331.
