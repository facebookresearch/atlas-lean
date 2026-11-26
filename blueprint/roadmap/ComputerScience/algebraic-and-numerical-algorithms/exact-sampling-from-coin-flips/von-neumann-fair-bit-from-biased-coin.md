# Von Neumann's extractor: an exact fair bit from a biased coin

*Von Neumann's procedure* reads coin flips in consecutive pairs, discards every pair of equal flips, and outputs the first flip of the first unequal pair; it is a DDG tree over $\{0,1\}$. Run on independent flips of a coin with $\Pr[1] = \rho$:

1. if $0 < \rho < 1$, it outputs a uniformly random bit (each value with probability exactly $1/2$), and its expected number of flips is exactly $1/(\rho(1-\rho))$;
2. there exists a DDG tree whose output law on independent $\rho$-coin flips is the uniform distribution on $\{0,1\}$ if and only if $0 < \rho < 1$.

## Proof sketch

Each pair is unequal with probability $2\rho(1-\rho)$, and given that it is unequal the outcomes $01$ and $10$ are equally likely, so the output is fair. The number of pairs read is geometric with success probability $2\rho(1-\rho)$, giving $2/(2\rho(1-\rho))$ expected flips. For $\rho \in \{0,1\}$ the flip sequence is deterministic, so every tree outputs each value with probability $0$ or $1$ and cannot output a fair bit.

## Depends on

- [Discrete distribution generating (DDG) tree](ddg-tree.md)

## Proof depends on

- [Discrete distribution generating (DDG) tree](ddg-tree.md)

## Sources

- J. von Neumann, "Various Techniques Used in Connection with Random Digits", in "Monte Carlo Method", National Bureau of Standards Applied Mathematics Series 12, 1951, pp. 36-38 (the procedure that rejects equal pairs of tosses and is rigorously unbiased).
