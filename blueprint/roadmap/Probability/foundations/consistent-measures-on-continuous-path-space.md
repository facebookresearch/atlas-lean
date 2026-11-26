# Extension of consistent measures on the canonical filtration of continuous paths

Let $E$ be a Polish space, $\Omega=C([0,\infty),E)$ with coordinate maps $X_t(\omega)=\omega(t)$, $\mathcal F_t=\sigma(X_s:s\le t)$ and $\mathcal F=\sigma\bigl(\bigcup_{t\ge0}\mathcal F_t\bigr)$. Let $P_t$, $t\ge0$, be probability measures on $(\Omega,\mathcal F_t)$ that are consistent: $P_u$ restricted to $\mathcal F_t$ is $P_t$ whenever $t\le u$. Then there is a unique probability measure $P$ on $(\Omega,\mathcal F)$ whose restriction to $\mathcal F_t$ is $P_t$ for every $t\ge0$.

## Proof depends on

- [Kolmogorov extension theorem](kolmogorov-extension-theorem/kolmogorov-extension.md)
- [Dynkin's π–λ theorem](../../MeasureTheory/measurable-spaces/pi-systems-and-the-theorem/dynkin-s-pi-lambda-theorem/induction-on-inter.md)

## Expansion

A proof page must identify $\mathcal F_t$ with the preimage of the Borel $\sigma$-field of the Polish space $C([0,t],E)$ under restriction; reduce to integer times; show that the set function defined by the $P_n$ on the algebra $\bigcup_n\mathcal F_n$ is countably additive, by inner regularity of finite Borel measures on the Polish spaces $C([0,n],E)$ and the surjectivity and continuity of the restriction maps, as in the proof of the Kolmogorov extension theorem; extend it by Carathéodory's theorem; and prove uniqueness by the $\pi$–$\lambda$ theorem. It should note that the consistency hypothesis alone does not suffice for an arbitrary filtered space: the topological structure of the path space is used.

## Sources

- D. W. Stroock and S. R. S. Varadhan, *Multidimensional Diffusion Processes*, Springer, 1979, Chapter 1.
