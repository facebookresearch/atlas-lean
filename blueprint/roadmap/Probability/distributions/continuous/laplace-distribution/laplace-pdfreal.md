# Density of the Laplace distribution

The Laplace distribution with location $m$ and scale $b > 0$ has density

$$
\mathrm{Lap}(z \mid m, b) = \frac{1}{2b} \exp\Big(-\frac{|z - m|}{b}\Big), \qquad z \in \mathbb{R}.
$$

Its variance is $2b^2$. It is the symmetric version of the exponential distribution.

## Background

- [The Laplace density](../../../../ComputerScience/machine-learning/supervised-learning/least-squares-ridge-and-lasso-regression/laplace-pdf.md): the same density, centred at $0$, used there as a prior for the lasso.

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/privacybook.html>, Definition 3.2 (centred at $0$).
