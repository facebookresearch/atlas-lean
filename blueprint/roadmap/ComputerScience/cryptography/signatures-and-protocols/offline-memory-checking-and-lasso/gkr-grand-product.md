# Grand products via a layered binary-tree circuit and GKR

The product of $N=2^{s}$ field elements is computed by a depth-$s$ binary tree of multiplication gates. Applying the GKR protocol, each layer's multilinear extension satisfies $\widetilde{V}_{i}(r)=\sum_{x\in\{0,1\}^{i}}\widetilde{\mathrm{eq}}(r,x)\widetilde{V}_{i+1}(x,0)\widetilde{V}_{i+1}(x,1)$, reducing a claim about layer $i$ to one about layer $i+1$ by a sum-check of $i$ rounds of degree $3$ and a two-to-one line reduction. The whole product claim is reduced to one evaluation of the multilinear extension of the inputs using $O(s^{2})$ rounds, a prover performing $O(N)$ field operations, and soundness error $O(s^{2}/|\mathbb{F}|)$.

## Proof sketch

The layer identity is the multilinear-extension form of $V_i(x)=V_{i+1}(x,0)V_{i+1}(x,1)$. Sum-check reduces it to the two points $(r',0)$ and $(r',1)$, combined by restricting to the line through them. Linear-time proving uses the folding technique for products of multilinear functions.

## Depends on

- [The multilinear equality polynomial on the Boolean hypercube](../plonkish-polynomial-iops/eq-polynomial.md)

## Proof depends on

- [The sum-check protocol](../../../../TheoryOfComputation/randomized-and-quantum-complexity/interactive-proofs/the-sum-check-protocol.md)

## Sources

- Justin Thaler, "Time-Optimal Interactive Proofs for Circuit Evaluation", CRYPTO (2013).
- Shafi Goldwasser, Yael Tauman Kalai, Guy N. Rothblum, "Delegating Computation: Interactive Proofs for Muggles", JACM (2015).
- Srinath Setty, Justin Thaler, Riad Wahby, "Unlocking the Lookup Singularity with Lasso", EUROCRYPT (2024), IACR ePrint 2023/1216.
