# Tillich–Zémor hypergraph product codes and the square-root distance barrier

Let $H_1 \in \mathbb{F}_2^{m_1 \times n_1}$ and $H_2 \in \mathbb{F}_2^{m_2 \times n_2}$ be parity-check matrices of classical LDPC codes with distances $d_1, d_2$ and with transposed codes of distances $d_1^{\top}, d_2^{\top}$. The **hypergraph product** is the CSS code with

$$
H_X = \bigl( H_1 \otimes I_{n_2} \ \big|\ I_{m_1} \otimes H_2^{\top} \bigr), \qquad H_Z = \bigl( I_{n_1} \otimes H_2 \ \big|\ H_1^{\top} \otimes I_{m_2} \bigr),
$$

on $n = n_1 n_2 + m_1 m_2$ qubits. It is LDPC, and its distance is $\min(d_1, d_2, d_1^{\top}, d_2^{\top})$. Taking good classical expander codes gives quantum LDPC codes with $k = \Theta(n)$ and $d = \Theta(\sqrt{n})$.

## Proof sketch

The commutation $H_X H_Z^{\top} = H_1 \otimes H_2^{\top} + H_1 \otimes H_2^{\top} = 0$ is immediate. The code is the tensor product of the two length-one chain complexes, and the Künneth formula identifies its homology with the tensor product of the homologies, which gives $k$. The distance bound follows by projecting a minimal-weight logical operator onto rows and columns of the product grid.

## Depends on

- [Quantum LDPC code families and asymptotically good quantum codes](../../../QuantumInformation/quantum-error-correction/homological-quantum-ldpc-codes/quantum-ldpc-code-families-and-good-codes.md)

## Sources

- J.-P. Tillich, G. Zémor, "Quantum LDPC codes with positive rate and minimum distance proportional to the square root of the blocklength", IEEE Transactions on Information Theory 60 (2014) 1193-1202.
