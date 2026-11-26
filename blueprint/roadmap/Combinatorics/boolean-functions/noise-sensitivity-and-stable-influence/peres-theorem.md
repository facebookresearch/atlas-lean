# Peres's theorem: linear threshold functions have noise sensitivity O(√δ)

Every linear threshold function $f : \{-1,1\}^n \to \{-1,1\}$ satisfies $\mathrm{NS}_\delta[f] \le 1/\sqrt{\lfloor 1/\delta \rfloor}$ for $0 < \delta \le 1/2$, and hence $\mathrm{NS}_\delta[f] \le \sqrt{3/2}\,\sqrt\delta$ for $0 \le \delta \le 1/2$. In particular the class of all linear threshold functions (over all $n$) is uniformly noise-stable.

## Proof sketch

Linear threshold functions are closed under negating, identifying and adding dummy variables, and are unate, so their total influence on $m$ variables is at most $\sqrt m$. The class theorem gives $\mathrm{NS}_\delta \le \sqrt m/m = 1/\sqrt m$ with $m = \lfloor 1/\delta\rfloor$.

## Depends on

- [Noise sensitivity](noise-sensitivity.md)
- [Linear threshold function](../majority-is-least-stable-conjecture/is-linear-threshold-function.md)

## Proof depends on

- [Noise sensitivity of a class from bounds on total influence](noise-sensitivity-from-total-influence.md)
- [Unate functions have total influence at most √(n·Var)](../influences-isoperimetry-and-elections/unate-functions-have-total-influence-at-most-sqrt-n.md)
- [Linear threshold functions are unate](../influences-isoperimetry-and-elections/linear-threshold-functions-are-unate.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
