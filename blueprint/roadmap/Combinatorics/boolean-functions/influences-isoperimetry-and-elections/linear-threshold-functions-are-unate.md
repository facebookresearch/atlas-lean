# Linear threshold functions are unate

Every linear threshold function $f(x) = \mathrm{sgn}(a_0 + \sum_i a_i x_i)$ (with the linear form nonzero on the cube) is unate in every direction: it is nondecreasing in $x_i$ if $a_i \ge 0$ and nonincreasing if $a_i \le 0$.

## Proof sketch

Changing $x_i$ from $-1$ to $1$ changes the linear form by $2a_i$, so its sign moves monotonically in the direction of $a_i$.

## Depends on

- [Linear threshold function](../majority-is-least-stable-conjecture/is-linear-threshold-function.md)
- [Unate Boolean function](../unate-and-monotone-boolean-functions/is-unate-bool-fun.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
