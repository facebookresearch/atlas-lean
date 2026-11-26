# Two-inequality semi-unification

*Two-inequality semi-unification* is the decision problem: given two pairs $(\sigma_1, \tau_1)$ and $(\sigma_2, \tau_2)$ of simple types (types built from type variables
by $\to$ alone), are there substitutions $\varphi$, $\psi_1$, $\psi_2$ of simple types for type variables with

$$\psi_1(\varphi(\sigma_1)) = \varphi(\tau_1) \quad\text{and}\quad \psi_2(\varphi(\sigma_2)) = \varphi(\tau_2)?$$

It combines first-order unification (for $\varphi$) with first-order matching (for $\psi_1$, $\psi_2$). An instance is *left-uniform* if $\sigma_1 = \sigma_2$.

## Sources

- A. Dudenhefner, "The undecidability of System F typability and type checking for reductionists", *Proceedings of the 36th Annual ACM/IEEE Symposium on Logic in Computer Science (LICS)*, 2021, <https://ps.uni-saarland.de/Publications/documents/Dudenhefner_2021_SystemF.pdf>: Problem 30 (two-inequality semi-unification) and Problem 34 (the left-uniform restriction).
