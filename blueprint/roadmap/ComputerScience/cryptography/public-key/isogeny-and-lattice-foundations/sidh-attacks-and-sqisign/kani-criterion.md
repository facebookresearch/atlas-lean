# Kani's lemma: isogeny diamonds give isogenies of abelian surfaces

Let $f:A\to B$, $g:A\to C$, $f':C\to D$, $g':B\to D$ be isogenies of elliptic curves forming a commutative diamond $g'\circ f=f'\circ g$, with $\deg f=\deg f'=a$, $\deg g=\deg g'=b$ and $\gcd(a,b)=1$. Then

$$
F=\begin{pmatrix}f & \hat{g}'\\ -g & \hat{f}'\end{pmatrix}:A\times D\to B\times C
$$

is an $N$-isogeny with $N=a+b$, i.e., $\hat{F}F=[N]$ for the dual $\hat{F}$ with respect to the product principal polarizations, and $\ker F=\{(\hat{f}(x),g'(x)):x\in B[N]\}$. In particular, if $f$ is known on $B[N]$-relevant torsion, $\ker F$ is computable, and $F$ can be evaluated by $(N,N)$-isogeny algorithms on abelian surfaces (or higher-dimensional analogues), from which $f$ is read off as a component.

## Proof sketch

Compute $\hat{F}=\begin{pmatrix}\hat{f} & -\hat{g}\\ g' & f'\end{pmatrix}$ and multiply: the diagonal entries are $\hat{f}f+\hat{g}g=[a]+[b]$ and $g'\hat{g}'+f'\hat{f}'=[b]+[a]$, while the off-diagonal entries vanish because $\hat{f}\hat{g}'=\hat{g}\hat{f}'$ is the dual of the diamond relation. For the kernel, $F(\hat{f}(x),g'(x))=([a]x+[b]x,\,-g\hat{f}x+\hat{f}'g'x)=(0,0)$ for $x\in B[N]$, using $\hat{f}'g'=g\hat{f}$; a counting argument shows these points form all of $\ker F$, of order $N^{2}$.

## Depends on

- [Supersingular elliptic curves and isogenies](../supersingular-isogenies-and-quaternion-orders/supersingular-curves.md)

## Proof depends on

- [Supersingular elliptic curves and isogenies](../supersingular-isogenies-and-quaternion-orders/supersingular-curves.md)

## Sources

- Ernst Kani, "The Number of Curves of Genus Two with Elliptic Differentials", Journal für die reine und angewandte Mathematik 485 (1997).
- Damien Robert, "Breaking SIDH in Polynomial Time", EUROCRYPT (2023), IACR ePrint 2022/1038.
- Wouter Castryck, Thomas Decru, "An Efficient Key Recovery Attack on SIDH", EUROCRYPT (2023), IACR ePrint 2022/975.
