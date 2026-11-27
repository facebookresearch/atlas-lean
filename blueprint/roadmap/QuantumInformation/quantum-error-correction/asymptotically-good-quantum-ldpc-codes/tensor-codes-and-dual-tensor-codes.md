# Tensor codes and dual tensor codes

For linear codes $C_A \subseteq \mathbb{F}_2^{A}$ and $C_B \subseteq \mathbb{F}_2^{B}$, the *tensor code* $C_A \otimes C_B \subseteq \mathbb{F}_2^{A \times B}$ consists of the $A \times B$ matrices all of whose columns lie in $C_A$ and rows lie in $C_B$. The *dual tensor code* is

$$
C_A \boxplus C_B := C_A \otimes \mathbb{F}_2^{B} + \mathbb{F}_2^{A} \otimes C_B = (C_A^\perp \otimes C_B^\perp)^\perp ,
$$

the matrices that are a sum of a matrix with columns in $C_A$ and a matrix with rows in $C_B$. The rank of $C_A \otimes C_B$ is $\dim C_A \cdot \dim C_B$.

## Depends on

- [Linear code](../../../InformationTheory/error-correcting-codes/linear-codes/linear-code.md)

## Sources

- Pavel Panteleev, Gleb Kalachev, "Asymptotically good quantum and locally testable classical LDPC codes", STOC (2022); arXiv:2111.03654.
- Anthony Leverrier, Gilles Zemor, "Quantum Tanner codes", FOCS (2022); arXiv:2202.13641.
