# Moments from generating functions and Laplace–Stieltjes transforms

For a nonnegative integer-valued random variable $X$ with generating function $P_X(z) = E[z^X]$: $P_X(1) = 1$, $P_X(0) = P(X = 0)$ and $P_X^{(k)}(1) = E[X(X - 1)\cdots(X - k + 1)]$, the derivatives taken from the left at $1$ and allowed to be infinite. For a nonnegative random variable $X$ with Laplace–Stieltjes transform $\tilde X(s) = E[e^{-sX}]$, $s \ge 0$: $\tilde X(0) = 1$ and $\tilde X^{(k)}(0) = (-1)^k E[X^k]$, the derivatives taken from the right at $0$. For independent $X$ and $Y$ the transform of $X + Y$ is the product of the transforms, and for a mixture equal to $X$ with probability $q$ and to $Y$ otherwise it is $q\tilde X + (1 - q)\tilde Y$; the same holds for generating functions.

## Depends on

- [Probability generating function](../../characteristic-functions/probability-generating-functions/pgf.md)
- [The generating function at 0](../../characteristic-functions/probability-generating-functions/pgf-zero.md)
- [The generating function at 1](../../characteristic-functions/probability-generating-functions/pgf-one.md)
- [Generating function of a sum of independent variables](../../characteristic-functions/probability-generating-functions/pgf-add-of-indep-fun.md)

## Sources

- I. Adan and J. Resing, *Queueing Systems*, lecture notes, Eindhoven University of Technology, <https://www.win.tue.nl/~iadan/queueing.pdf>, Sections 2.2 and 2.3.
