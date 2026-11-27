# Kani's lemma: isogeny diamonds give isogenies of abelian surfaces

Let $f:A\to B$, $g:A\to C$, $f':C\to D$, $g':B\to D$ be isogenies of elliptic curves forming a commutative diamond $g'\circ f=f'\circ g$, with $\deg f=\deg f'=a$, $\deg g=\deg g'=b$, such that $N=a+b$ is prime to the characteristic of the base field. Then

$$
F=\begin{pmatrix}f & \hat{g}'\\ -g & \hat{f}'\end{pmatrix}:A\times D\to B\times C
$$

is an $N$-isogeny, i.e., $\hat{F}F=[N]$ for the dual $\hat{F}$ with respect to the product principal polarizations. If moreover $\gcd(a,b)=1$, then $\ker F=\{(\hat{f}(x),g'(x)):x\in B[N]\}$. In particular, $\ker F$ is computable from the images of a basis of $B[N]$ under $\hat{f}$ and $g'$, and $F$ can be evaluated by $(N,N)$-isogeny algorithms on abelian surfaces (or higher-dimensional analogues); $f=\pi\circ F\circ\iota$ for the inclusion $\iota:A\to A\times D$ and the projection $\pi:B\times C\to B$.

## Proof sketch

Compute $\hat{F}=\begin{pmatrix}\hat{f} & -\hat{g}\\ g' & f'\end{pmatrix}$ and multiply: the diagonal entries are $\hat{f}f+\hat{g}g=[a]+[b]$ and $g'\hat{g}'+f'\hat{f}'=[b]+[a]$, while the off-diagonal entries vanish because $\hat{f}\hat{g}'=\hat{g}\hat{f}'$ is the dual of the diamond relation. For the kernel, $F(\hat{f}(x),g'(x))=([a]x+[b]x,\,-g\hat{f}x+\hat{f}'g'x)=(0,0)$ for $x\in B[N]$, using $\hat{f}'g'=g\hat{f}$; when $\gcd(a,b)=1$ the map $x\mapsto(\hat{f}(x),g'(x))$ is injective, since $\ker\hat{f}\subseteq B[a]$ and $\ker g'\subseteq B[b]$, and because $N$ is prime to the characteristic, $\#B[N]=N^{2}=\deg F$, so these points form all of $\ker F$.

## Depends on

- [Supersingular elliptic curves and isogenies](../supersingular-isogenies-and-quaternion-orders/supersingular-curves.md)

## Sources

- Ernst Kani, "The Number of Curves of Genus Two with Elliptic Differentials", Journal für die reine und angewandte Mathematik 485 (1997).
- Damien Robert, "Breaking SIDH in Polynomial Time", EUROCRYPT (2023), IACR ePrint 2022/1038.
- Pierrick Dartois, Antonin Leroux, Damien Robert, Benjamin Wesolowski, "SQIsignHD: New Dimensions in Cryptography", EUROCRYPT (2024), IACR ePrint 2023/436, Lemma 3.2.3 and Appendix A.1.
- Wouter Castryck, Thomas Decru, "An Efficient Key Recovery Attack on SIDH", EUROCRYPT (2023), IACR ePrint 2022/975.
