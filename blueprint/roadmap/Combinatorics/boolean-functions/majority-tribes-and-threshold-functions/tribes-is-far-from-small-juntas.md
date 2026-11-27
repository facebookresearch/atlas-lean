# Tribes is far from every small junta

For the nearly balanced Tribes function on $n = sw$ bits, with $n > 1$, every Boolean function that depends on at most $3n/4$ of the coordinates disagrees with Tribes on at least an $\varepsilon_0$ fraction of inputs, for a universal constant $\varepsilon_0 > 0$ (O'Donnell, Ex. 4.15). Hence Tribes, which has total influence $O(\log n)$, is not close to any junta on a constant fraction fewer coordinates; Friedgut's junta theorem is thus sharp in its dependence on the total influence.

## Proof sketch

A junta on $J$ ignores the bits outside $J$, so it cannot track Tribes on inputs where a tribe meeting the complement of $J$ is decisive; since at least a quarter of the bits lie outside $J$, a constant fraction of tribes have a bit outside $J$, and with constant probability exactly one such tribe decides the value. Averaging over the hidden bits gives constant disagreement.

## Depends on

- [The Tribes function](the-tribes-function.md)
- [Relative Hamming distance on the Boolean cube](../../../TheoryOfComputation/pcp-and-inapproximability/blum-luby-rubinfeld-linearity-test/bool-dist.md)

## Proof depends on

- [Fourier coefficients and influences of Tribes](fourier-coefficients-and-influences-of-tribes.md)

## Sources

- R. O'Donnell, "Analysis of Boolean Functions", Cambridge University Press, 2014.
