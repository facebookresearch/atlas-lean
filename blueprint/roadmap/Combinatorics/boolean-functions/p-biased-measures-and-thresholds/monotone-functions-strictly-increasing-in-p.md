# Nonconstant monotone functions have strictly increasing p-biased probability

If $f : \{0,1\}^n \to \{0,1\}$ is monotone and nonconstant, then $p \mapsto \Pr_p[f = 1]$ is strictly increasing on $[0, 1]$, from $0$ to $1$.

## Proof sketch

By Margulis–Russo the derivative is the expected number of pivotal coordinates; a nonconstant monotone function has a pivotal coordinate at some input, which has positive probability for $0 < p < 1$, and continuity handles the endpoints.

## Depends on

- [Expectation under the p-biased product measure](expectation-under-the-p-biased-measure.md)

## Proof depends on

- [The Margulis–Russo formula](margulis-russo-formula.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
