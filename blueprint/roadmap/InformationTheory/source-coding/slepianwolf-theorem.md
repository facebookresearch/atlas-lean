# Slepian–Wolf theorem

Let $(X_i, Y_i)$ be independent and identically distributed pairs on finite alphabets, with $X^n$ and $Y^n$
encoded separately at rates $R_1$ and $R_2$ and decoded jointly. Vanishing error probability is achievable if
$R_1 > H(X \mid Y)$, $R_2 > H(Y \mid X)$ and $R_1 + R_2 > H(X,Y)$, and only if
$R_1 \ge H(X \mid Y)$, $R_2 \ge H(Y \mid X)$ and $R_1 + R_2 \ge H(X,Y)$.

## Expansion

This node states a precise result. A good expansion adds a page for each of the following
prerequisites and links it under the dependency sections below:

- Proof prerequisite: AEP and typical sets (finite iid).
- Proof prerequisite: Joint typicality (finite iid).
- Proof prerequisite: Fano's inequality for joint distributions with zero-probability outcomes (the linked version assumes strictly positive probabilities).

## Depends on

- [Mutual information of a finite joint law](../entropy-and-mutual-information/conditional-mutual-information/finite-mutual-information.md)

## Proof depends on

- [Fano's inequality, general form](../information-inequalities/fano-s-inequality/fano-inequality-general.md)

## Sources

- Y. Polyanskiy and Y. Wu, *Information Theory: From Coding to Learning*, Cambridge University Press, 2025 (author draft), Theorem 11.16. <https://people.lids.mit.edu/yp/homepage/data/itbook-export.pdf>
