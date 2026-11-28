# Global asymptotic stability of linear plants with ReLU neural-network feedback is undecidable

No algorithm decides, given rational matrices A, B and a ReLU neural network with rational weights and biases, whether the closed loop x⁺ = Ax + Bψ(x) is globally asymptotically stable.

**Theorem (Korda).** A *ReLU neural network* $\psi : \mathbb R^n \to \mathbb R^m$ is a map

$$
\psi(x) = W_N\bigl(\cdots \rho(W_2\, \rho(W_1 x + b_1) + b_2) \cdots\bigr) + b_N
$$

with weight matrices $W_i$, bias vectors $b_i$ and the activation $\rho(z) = \max(z, 0)$ applied componentwise. The following problem is undecidable in the Turing model of computation: given $A \in \mathbb Q^{n \times n}$, $B \in \mathbb Q^{n \times m}$ and the rational weights and biases of a ReLU neural network $\psi$, is the closed-loop system

$$
x_{k+1} = A x_k + B \psi(x_k)
$$

[globally asymptotically stable](global-asymptotic-stability-of-discrete-time-maps.md)?

The dimensions $n$, $m$, the number of layers and their widths are part of the input; the instances used in the proof have $A = 0$, $B$ the identity and two layers.

## Depends on

- [Global asymptotic stability of a discrete-time system](global-asymptotic-stability-of-discrete-time-maps.md)
- [Decidability by multi-stack machines](../../../../TheoryOfComputation/computability/decidable-and-recognizable-predicates/tm2-decidable.md)

## Proof depends on

- [Global asymptotic stability of saturated linear systems is undecidable](stability-of-saturated-linear-systems-undecidable.md)

## Proof sketch

The proof reduces stability of saturated linear systems $x^+ = \mathrm{sat}(Dx)$, $D \in \mathbb Q^{n \times n}$, where $\mathrm{sat}(z) = \min(\max(z, -1), 1)$ componentwise. Since $\mathrm{sat}(z) = \mathrm{ReLU}(z + 1) - \mathrm{ReLU}(z - 1) - 1$, the saturated system is the closed loop with $A = 0$, $B = I$ and the two-layer network with

$$
W_1 = \begin{bmatrix} D \\ D \end{bmatrix}, \quad b_1 = \begin{bmatrix} \mathbf 1 \\ -\mathbf 1 \end{bmatrix}, \quad W_2 = [\, I, \; -I \,], \quad b_2 = -\mathbf 1 .
$$

So a decision procedure for the closed loops would decide stability of saturated linear systems. The source contrasts this with its sum-of-squares method, which gives sufficient conditions for stability: the undecidability shows that no degree bound for the certificates is computable from the data, even for linear plants.

## Sources

- Milan Korda, "Stability and performance verification of dynamical systems controlled by neural networks: algorithms and complexity", *IEEE Control Systems Letters* 6, 2022, pp. 3265–3270, <https://doi.org/10.1109/LCSYS.2022.3181806>; read as arXiv:2102.02273v5, <https://arxiv.org/abs/2102.02273v5>: Theorem 3 of that version and its proof, in Section 3 (subsection "Checking stability is undecidable"), with the network class of Section 2.
