# Entropy power is not supermodular

For real random variables with densities, write $H$ for differential entropy, $H(X) = -\int f\log f$ with $f$ the density of $X$. There are independent real random variables $X_1, X_2, X_3$ with densities such that $X_2$, $X_1 + X_2$, $X_2 + X_3$ and $X_1 + X_2 + X_3$ have densities $f$ with $f\log f$ integrable, for which $e^{2H(X_1+X_2)} + e^{2H(X_2+X_3)} > e^{2H(X_1+X_2+X_3)} + e^{2H(X_2)}$. Madiman and Ghassemi (2019) showed that the inequality can fail.

## Sources

- Problem: Problems from the AIM Workshop on Algorithmic Convex Geometry (compiled by N. Goyal), Problem 6 (M. Madiman), https://aimath.org/WWN/convexgeometry/convexgeometry.pdf.
- Resolution: M. Madiman and F. Ghassemi, Combinatorial entropy power inequalities: a preliminary study of the Stam region, IEEE Trans. Inform. Theory 65 (2019), no. 3, 1375-1386, arXiv:1704.01177, https://doi.org/10.1109/TIT.2018.2854545.
