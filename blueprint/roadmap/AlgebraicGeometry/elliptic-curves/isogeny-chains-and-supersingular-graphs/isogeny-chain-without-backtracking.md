# Chain of isogenies without backtracking

A chain of $\ell$-isogenies backtracks at a step when the next isogeny has the same kernel as the dual of the previous one. The notion is about the isogenies themselves, over an algebraically closed field, not about walks in a graph of isomorphism classes.

Let $k$ be an algebraically closed field and $\ell$ a prime different from $\operatorname{char}k$. A *chain of $\ell$-isogenies of length $m$* is a sequence of elliptic curves $E_0,\dots,E_m$ over $k$ with separable [isogenies](../isogenies-of-elliptic-curves/isogeny-of-elliptic-curves.md) $\varphi_i\colon E_{i-1}\to E_i$ of degree $\ell$, $1\le i\le m$; its composite is $\varphi_m\circ\cdots\circ\varphi_1$. The chain *backtracks at step* $i$, for $1\le i\le m-1$, if

$$
\ker\varphi_{i+1}=\ker\hat\varphi_i\subseteq E_i(k),
$$

where $\hat\varphi_i\colon E_i\to E_{i-1}$ is the [dual](../isogenies-of-elliptic-curves/dual-isogeny.md) of $\varphi_i$, itself separable of degree $\ell$. It is *without backtracking* if it backtracks at no step; a chain of length $1$ is without backtracking.

Equivalently, the chain backtracks at step $i$ exactly when $\varphi_{i+1}=\iota\circ\hat\varphi_i$ for an isomorphism $\iota\colon E_{i-1}\to E_{i+1}$; when $E_{i+1}=E_{i-1}$ this reads $\varphi_{i+1}=\varepsilon\circ\hat\varphi_i$ with $\varepsilon\in\operatorname{Aut}(E_{i+1})$, the form in which Costache, Feigon, Lauter, Massierer and Puskás state the condition.

From a fixed source curve, isogenies with different kernels are different edges, although several of them can end at the same vertex. A chain gives a walk in the $\ell$-isogeny graph of isomorphism classes. Reversing an edge can fail to be well defined on isogenies taken up to an isomorphism of the target when the target has automorphisms other than $\pm1$: if $\varphi'=\varepsilon\circ\varphi$ with $\varepsilon\in\operatorname{Aut}(E')$, then $\hat\varphi'=\hat\varphi\circ\hat\varepsilon=\hat\varphi\circ\varepsilon^{-1}$, whose kernel is $\varepsilon(\ker\hat\varphi)$, which differs from $\ker\hat\varphi$ when $\varepsilon$ moves it. When every curve on the chain has automorphism group $\{\pm1\}$, backtracking can be read off a walk that records its edges, that is, the kernel taken at each step, but not off the sequence of vertices alone: for $p=13$ and $\ell=2$ the supersingular $2$-isogeny graph has one vertex and three edges, and after a first step the dual edge and either other edge give the same vertex sequence, one backtracking and one not.

## Depends on

- [Isogeny of elliptic curves](../isogenies-of-elliptic-curves/isogeny-of-elliptic-curves.md)
- [Existence and uniqueness of the dual isogeny](../isogenies-of-elliptic-curves/dual-isogeny.md)

## Proof depends on

- [Every finite subgroup is the kernel of a separable isogeny](../isogenies-of-elliptic-curves/separable-isogeny-with-prescribed-kernel.md)
- [Composition, sum and double-dual rules for dual isogenies](../isogenies-of-elliptic-curves/properties-of-the-dual-isogeny.md)

## Expansion

A definition. The equivalent form uses that separable isogenies with the same kernel differ by an isomorphism of the target, which is the uniqueness clause of the page on prescribed kernels. Charles, Goren and Lauter phrase backtracking in that form in the proof of their Proposition 1. The remark on reversing edges uses $\widehat{\varepsilon\circ\varphi}=\hat\varphi\circ\hat\varepsilon$ and $\hat\varepsilon=\varepsilon^{-1}$ for an automorphism; Sutherland and Galbraith discuss the resulting asymmetry of the graph at $j=0$ and $j=1728$.

## Sources

- Anamaria Costache, Brooke Feigon, Kristin Lauter, Maike Massierer, Anna Puskás, "Ramanujan graphs in cryptography", in *Research Directions in Number Theory (Women in Numbers IV)*, Association for Women in Mathematics Series 19, Springer (2019) 1–40, [doi:10.1007/978-3-030-19478-9_1](https://doi.org/10.1007/978-3-030-19478-9_1); numbers from arXiv:1806.05709v2, Definition 4.1.
- Denis X. Charles, Eyal Z. Goren, Kristin E. Lauter, "Cryptographic Hash Functions from Expander Graphs", *Journal of Cryptology* 22 (2009) 93–113, [doi:10.1007/s00145-007-9002-x](https://doi.org/10.1007/s00145-007-9002-x), Proposition 1 and its proof.
- Andrew V. Sutherland, *18.783 Elliptic Curves*, MIT lecture notes, Spring 2022, [Lecture 22: Isogeny volcanoes](https://math.mit.edu/classes/18.783/2022/LectureNotes22.pdf), Remark 22.2.
- Steven D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press (2012); extended and corrected version 2.0 of Chapter 25, [author's copy](https://www.math.auckland.ac.nz/~sgal018/crypto-book/ch25.pdf) (numbering of the extended version), Exercise 25.1.1 and Remark 25.3.2.
