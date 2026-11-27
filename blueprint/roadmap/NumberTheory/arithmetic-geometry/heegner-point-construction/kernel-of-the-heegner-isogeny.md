# The Heegner isogeny is cyclic of degree $N$

Let $K \subset \mathbb{C}$ be an imaginary quadratic field with ring of integers $\mathcal{O}_K$, and let
$\mathcal{N}$ be a nonzero ideal of $\mathcal{O}_K$ such that $\mathcal{O}_K/\mathcal{N}$ is cyclic of order $N$, as
given by [the Heegner hypothesis](ideal-of-index-n-under-the-heegner-hypothesis.md). Let
$\mathcal{N}^{-1} = \{x \in K : x\mathcal{N} \subseteq \mathcal{O}_K\}$. Then $\mathcal{O}_K$ and
$\mathcal{N}^{-1}$ are lattices in $\mathbb{C}$ with $\mathcal{O}_K \subseteq \mathcal{N}^{-1}$, and the quotient
$\mathcal{N}^{-1}/\mathcal{O}_K$ is cyclic of order $N$. Hence the map
$\mathbb{C}/\mathcal{O}_K \to \mathbb{C}/\mathcal{N}^{-1}$ induced by the identity of $\mathbb{C}$ is an isogeny of
complex tori whose kernel $\mathcal{N}^{-1}/\mathcal{O}_K$ is cyclic of order $N$.

Miller and Gross assert that this isogeny is cyclic of degree $N$. The argument (worked out here): for fractional
ideals $J \subseteq I$ of the Dedekind domain $\mathcal{O}_K$ there is an isomorphism of $\mathcal{O}_K$-modules
$I/J \cong \mathcal{O}_K/JI^{-1}$, as both sides are locally isomorphic; with $I = \mathcal{N}^{-1}$ and
$J = \mathcal{O}_K$ it gives $\mathcal{N}^{-1}/\mathcal{O}_K \cong \mathcal{O}_K/\mathcal{N}$, which is cyclic of order $N$.

## Sources

- R. L. Miller, *Proving the Birch and Swinnerton-Dyer conjecture for specific elliptic curves of analytic rank zero
  and one*, LMS J. Comput. Math. 14 (2011), 327–350, doi:10.1112/S1461157011000180: §4, p. 335 ("Since $\mathcal{O}_K \subset \mathcal{N}^{-1}$, we have a cyclic $N$-isogeny
  $\mathbb{C}/\mathcal{O}_K \to \mathbb{C}/\mathcal{N}^{-1}$ of elliptic curves with CM by $\mathcal{O}_K$").
- B. H. Gross, *Kolyvagin's work on modular elliptic curves*, in *L-functions and arithmetic* (Durham, 1989),
  London Math. Soc. Lecture Note Ser. 153, Cambridge Univ. Press, 1991, 235–256: §1, p. 235 (the tori $\mathbb{C}/\mathcal{O}$ and $\mathbb{C}/\mathcal{N}^{-1}$ "define elliptic curves related by
  a cyclic $N$-isogeny"); §3, p. 238 ("The ideal $\mathcal{N}_n = \mathcal{N} \cap \mathcal{O}_n$ is an invertible
  $\mathcal{O}_n$-module with $\mathcal{O}_n/\mathcal{N}_n \simeq \mathbb{Z}/N\mathbb{Z}$"), whose case $n = 1$ is the ideal here.
