# Identifiable bidirected-tree and directed-cycle compartmental models

**Setting.** A linear compartmental model on a directed graph $G$ with vertices $1,\dots,n$ has state $x\in\mathbb R^n$, dynamics $\dot x=Ax+u$ and outputs $y_i=x_i$ for $i\in\mathrm{Out}$, where inputs $u_j$ act only on compartments $j\in\mathrm{In}$. The compartmental matrix has $A_{ij}=k_{ij}$ for each edge $j\to i$, and $A_{jj}=-k_{0j}-\sum_{i}k_{ij}$, where $k_{0j}>0$ only for compartments $j\in\mathrm{Leak}$. Eliminating unobserved states gives input–output equations whose coefficients are polynomials in the rate constants. The model is *generically locally identifiable* if the coefficient map is generically finite-to-one, so that the rates are determined by noise-free input–output data up to finitely many possibilities.

**Theorem 5.1.**
1. A bidirected-tree model (each edge of a tree present in both directions) with one input and one output is generically locally identifiable if and only if it has at most one leak and the distance from the input compartment to the output compartment is at most $1$.
2. A directed-cycle model $1\to2\to\dots\to n\to1$, with any numbers of inputs, outputs and leaks, is generically locally identifiable if and only if it is leak-interlacing: between any two leak compartments along the cycle there is an input or an output compartment.

Other identifiable families include the directed path $1\to\dots\to n$ with $\mathrm{In}=\{1\}$, $\mathrm{Out}=\{n\}$ and $\mathrm{Leak}=\{1,n\}$.

## Expansion

For one input and one output in compartment $i$ and $j$, the input–output equation is $\det(\partial I-A)\,y_j=(-1)^{i+j}\det\big((\partial I-A)^{(i,j)}\big)u_i$, so its coefficients are the characteristic-polynomial coefficients of $A$ and of the submatrix obtained by deleting row $i$ and column $j$. Generic local identifiability is equivalent to the Jacobian of this coefficient map having full rank at a generic parameter, which is how both classifications are established in the works the survey cites. Intuitively, on a directed cycle two consecutive leaks with no measured compartment between them can be traded against the flow on the arc between them without changing the observed dynamics, which is the obstruction that leak-interlacing removes.

## Sources

- N. Meshkat, A. Shiu, "Structural Identifiability of Compartmental Models: Recent Progress and Future Directions", *Current Opinion in Systems Biology* 42 (2025), 100559, Theorem 5.1 and Table 1 of Section 5, <https://doi.org/10.1016/j.coisb.2025.100559> (preprint arXiv:2507.04496).
