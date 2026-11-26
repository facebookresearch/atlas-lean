# Finite set of symbols of a term

The finite set of symbols occurring in a term $t$ of a
first-order language $L$, a finite subset of the function and relation symbols of $L$, is
defined by recursion on $t$: it is empty when $t$ is a variable, and when
$t = f(t_0, \dots, t_{l-1})$ for an $l$-ary function symbol $f$ it consists of $f$ together with
the symbols occurring in each of $t_0, \dots, t_{l-1}$.

## Sources

- D. van Dalen, *Logic and Structure*, 5th ed., Springer 2013, §3.1 (the finite set of symbols occurring in a finite derivation).
