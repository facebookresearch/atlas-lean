# The modular polynomial detects cyclic isogenies

Over an algebraically closed field whose characteristic does not divide $N$, the classical modular polynomial $\Phi_N$ vanishes at a pair of $j$-invariants exactly when the curves are related by a cyclic isogeny of degree $N$.

Let $N>1$ be an integer and let $\Phi_N(X,Y)\in\mathbb{Z}[X,Y]$ be the classical modular polynomial of level $N$, the minimal polynomial of $j(N\tau)$ over $\mathbb{C}(j(\tau))$, which has integer coefficients and is symmetric, $\Phi_N(X,Y)=\Phi_N(Y,X)$. Let $k$ be an algebraically closed field whose characteristic does not divide $N$, and let $E_1$, $E_2$ be elliptic curves over $k$. Then

$$
\Phi_N\bigl(j(E_1),j(E_2)\bigr)=0
$$

if and only if there is a [cyclic isogeny](../isogeny-chains-and-supersingular-graphs/cyclic-isogeny.md) $E_1\to E_2$ of degree $N$. For $N=\ell$ prime, $\Phi_\ell(j(E_1),Y)$ has degree $\ell+1$ in $Y$, and its roots, counted with multiplicity, correspond to the $\ell+1$ subgroups of order $\ell$ of $E_1$.

## Depends on

- [Isogeny of elliptic curves](isogeny-of-elliptic-curves.md)
- [Cyclic isogeny](../isogeny-chains-and-supersingular-graphs/cyclic-isogeny.md)

## Proof depends on

- [Counting subgroups of prime-power order in the torsion of an elliptic curve](../isogeny-chains-and-supersingular-graphs/number-of-cyclic-subgroups-of-prime-power-torsion.md)

## Expansion

Over $\mathbb{C}$ (Sutherland, Theorem 20.3, proved there for $N$ prime), curves are complex tori $\mathbb{C}/L$, cyclic $N$-isogenies correspond to cyclic sublattices of index $N$, and for $N$ prime $\Phi_N(j(\tau),Y)=(Y-j(N\tau))\prod_{k=0}^{N-1}\bigl(Y-j((\tau+k)/N)\bigr)$, whose $N+1$ factors correspond to the $N+1$ cyclic sublattices of index $N$. The extension to characteristic zero is the Lefschetz principle, and to characteristic $p\nmid N$ it is Igusa's theorem, as Sutherland states in Theorem 20.4 for curves over arbitrary such fields; over a field that is not algebraically closed one may have to replace a curve by a twist (Sutherland, Remark 20.5), which is why this page states the algebraically closed case. A good expansion adds a page defining $\Phi_N$ through the $j$-function and its coset product, a page for the lattice description of isogenies over $\mathbb{C}$, and a page for Igusa's reduction theorem for $X_0(N)$.

## Sources

- Andrew V. Sutherland, *18.783 Elliptic Curves*, MIT lecture notes, Fall 2023, [Lecture 20: The Hilbert class polynomial](https://math.mit.edu/classes/18.783/2023/LectureNotes20.pdf), Lemma 20.2, Theorems 20.3, 20.4 and 20.7, Remarks 20.5 and 20.6.
- Steven D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press (2012); extended and corrected version 2.0 of Chapter 25, [author's copy](https://www.math.auckland.ac.nz/~sgal018/crypto-book/ch25.pdf) (numbering of the extended version), Section 25.2, the paragraph on the modular polynomial (cited only for the geometric statement over an algebraically closed field).
- Andrew V. Sutherland, *18.783 Elliptic Curves*, MIT lecture notes, Spring 2022, [Lecture 22: Isogeny volcanoes](https://math.mit.edu/classes/18.783/2022/LectureNotes22.pdf), opening paragraph and Definition 22.1 (roots of $\Phi_\ell(j,Y)$ and subgroups of order $\ell$).
