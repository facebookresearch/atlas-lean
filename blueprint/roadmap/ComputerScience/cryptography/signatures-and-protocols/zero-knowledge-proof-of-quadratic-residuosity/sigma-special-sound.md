# Special soundness of the quadratic-residuosity protocol

The [quadratic-residuosity protocol](sigma.md) is specially sound with the [extractor](extract.md): if
$w_0^2 = u$ and $w_1^2 = u y$ then $(w_1 w_0^{-1})^2 = y$.

## Sources

- S. Goldwasser, S. Micali and C. Rackoff, "The knowledge complexity of interactive proof systems", SIAM J. Comput. 18 (1989), 186-208, Section 5, proof of Claim 1 ("it cannot be the case that both $u_i$ and $(u_i y)$ have
  square roots").
