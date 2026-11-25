# Skorokhod space D[0,T] with J1 metric

Let $T>0$. The Skorokhod space $D[0,T]$ is the set of càdlàg functions $f:[0,T]\to\mathbb R$: right-continuous on $[0,T)$ with left limits on $(0,T]$. Let $\Lambda_T$ be the set of order isomorphisms of $[0,T]$, the increasing homeomorphisms $\varphi$ with $\varphi(0)=0$ and $\varphi(T)=T$. The J1 distance is

$$d(f,g)=\inf_{\varphi\in\Lambda_T}\max\Bigl(\sup_{t\in[0,T]}|\varphi(t)-t|,\ \sup_{t\in[0,T]}|f(t)-g(\varphi(t))|\Bigr).$$

It is a metric on $D[0,T]$, with finite values since càdlàg functions are bounded. The inclusion of $C[0,T]$ with the uniform norm is $1$-Lipschitz, $d(f,g)\le\sup_t|f(t)-g(t)|$, by taking $\varphi=\mathrm{id}$. $D[0,T]$ carries the Borel $\sigma$-algebra of the topology of $d$.

## Expansion

A full page must establish the metric axioms (symmetry through $\varphi^{-1}$, the triangle inequality through composition, and $d(f,g)=0\Rightarrow f=g$ from right-continuity), finiteness, and the $1$-Lipschitz inclusion of $C[0,T]$. Separability and completeness under an equivalent metric, and the description of the Borel $\sigma$-algebra by evaluations, are separate pages.

## Sources

- P. Billingsley, *Convergence of Probability Measures*, 2nd ed., Wiley (1999), <https://en.wikipedia.org/wiki/Convergence_of_Probability_Measures> (book description), equation (12.13) (J1 metric).
