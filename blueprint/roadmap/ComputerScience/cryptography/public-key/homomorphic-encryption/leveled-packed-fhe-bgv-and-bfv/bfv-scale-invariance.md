# Scale-invariant BFV: leveled FHE without modulus switching

In the BFV scheme, multiplication computes $\lfloor\frac{t}{q}(\mathbf{c}\otimes\mathbf{c}')\rceil$ followed by relinearization. If the inputs have noise norms $V_1,V_2$ with respect to the scale $\Delta$, the output noise is bounded by $O(\delta_Rt\|s\|_1)\cdot(V_1+V_2)$ plus lower-order terms, i.e., noise grows by a fixed multiplicative factor per level independent of $q$. Hence, with a single modulus $q$, BFV evaluates circuits of multiplicative depth $L$ provided $\log q\gtrsim L\log(\delta_Rt\|s\|_1)+\log V_0+\log t$, and its security (for appropriately chosen parameters, including a variant based on standard LWE) relies on Ring-LWE together with circular security of the relinearization key.

## Proof sketch

Write $c_0+c_1s=\Delta m+v+qk$ for an integer polynomial $k$ of small norm. The scaled tensor product evaluates to $\Delta mm'$ plus error terms in which the large multiples $qk$ are divided by $q$ and multiplied by $t$, producing contributions proportional to $t\cdot(\|v\|+\|v'\|)\cdot\delta_R\|s\|_1$, while the term $vv'/\Delta$ is lower order. Rounding adds noise proportional to $\delta_R\|s\|_1^{2}$.

## Depends on

- [Ciphertext multiplication by tensoring](tensor-product-multiplication.md)
- [Relinearization by gadget key switching](relinearization.md)

## Proof depends on

- [Ciphertext multiplication by tensoring](tensor-product-multiplication.md)
- [Relinearization by gadget key switching](relinearization.md)

## Sources

- Junfeng Fan, Frederik Vercauteren, "Somewhat Practical Fully Homomorphic Encryption", IACR ePrint 2012/144 (2012).
- Zvika Brakerski, "Fully Homomorphic Encryption without Modulus Switching from Classical GapSVP", CRYPTO (2012).
