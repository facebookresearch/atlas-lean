# GMR's per-challenge simulator

In a finite commutative group $G$, for the statement $y$ and the bit $b$: draw a uniform $w \in G$
and output the commitment $w^2$ (bit $0$) or
$w^2 y^{-1}$ (bit $1$) together with the answer $w$.

## Sources

- S. Goldwasser, S. Micali and C. Rackoff, "The knowledge complexity of interactive proof systems", SIAM J. Comput. 18 (1989), 186-208, Section 5, proof of Theorem 1 (the machine $M$: "$u_{i+1} := w_{i+1}^2$" or
  "$u_{i+1} := w_{i+1}^2 y^{-1}$").
