# Shifting the Laplace density

For $b > 0$ and all $m, m', z$,

$$
\mathrm{Lap}(z \mid m, b) \le \exp\Big(\frac{|m - m'|}{b}\Big) \, \mathrm{Lap}(z \mid m', b),
$$

by the triangle inequality $|z - m'| \le |z - m| + |m - m'|$. This pointwise ratio bound is the whole
privacy proof of the [Laplace mechanism](../../../../ComputerScience/cryptography/laplace-and-exponential-mechanisms/README.md).

## Sources

- C. Dwork and A. Roth, *The Algorithmic Foundations of Differential Privacy*, Foundations and Trends in Theoretical Computer Science 9(3–4), 2014, <https://www.cis.upenn.edu/~aaroth/privacybook.html>, proof of Theorem 3.6.
