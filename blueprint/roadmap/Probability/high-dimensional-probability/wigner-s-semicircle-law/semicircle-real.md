# Semicircle distribution defined by its density

The Wigner semicircle distribution $\sigma$ is the measure on $\mathbb{R}$ given by
$\sigma(A) = \int_{A \cap [-2, 2]} \frac{\sqrt{4 - x^2}}{2\pi} \, dx$ for every measurable set
$A \subseteq \mathbb{R}$: Lebesgue measure on $[-2, 2]$ with the [semicircle density](semicircle-pdfreal.md). It is
a probability measure, since $\int_{-2}^{2} \sqrt{4 - x^2} \, dx = 2\pi$, and its moments are the Catalan numbers.

It is the same measure as the [semicircle distribution](semicircle-law.md) in the statement of
Wigner's semicircle law ([the two semicircle distributions agree](semicircle-law-eq-semicircle-real.md)).

## Sources

- T. Tao, *Topics in Random Matrix Theory*, Graduate Studies in Mathematics 132, American Mathematical Society, 2012, §2.4, equation (2.81).
