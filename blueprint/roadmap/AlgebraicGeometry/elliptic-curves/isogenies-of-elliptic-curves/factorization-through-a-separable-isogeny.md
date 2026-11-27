# An isogeny factors through a separable isogeny with smaller kernel

If the kernel of a separable isogeny $\varphi$ is contained in the kernel of an isogeny $\psi$ with the same domain, then $\psi$ factors uniquely as an isogeny composed after $\varphi$.

Let $\varphi\colon E_1\to E_2$ be a nonzero separable [isogeny](isogeny-of-elliptic-curves.md) and $\psi\colon E_1\to E_3$ an isogeny of elliptic curves over a field $k$, with $\ker\varphi\subseteq\ker\psi$. Then there is a unique isogeny $\lambda\colon E_2\to E_3$ with

$$
\psi=\lambda\circ\varphi .
$$

If $k$ is perfect and $\varphi$, $\psi$ are defined over $k$, then so is $\lambda$. The separability hypothesis is on $\varphi$, the isogeny factored through; $\psi$ may be inseparable or zero (then $\lambda=0$).

## Depends on

- [Isogeny of elliptic curves](isogeny-of-elliptic-curves.md)

## Proof depends on

None.

## Expansion

If $\psi=0$, take $\lambda=0$; it is the only choice, since $\varphi$ is surjective. Let $\psi\ne0$. Over $\bar k$, the extension $\bar k(E_1)/\varphi^*\bar k(E_2)$ is Galois with group the translations by $\ker\varphi$. Every $f\in\psi^*\bar k(E_3)$ is invariant under these translations, because $\ker\varphi\subseteq\ker\psi$ and $\psi$ is a homomorphism, so $\psi^*\bar k(E_3)\subseteq\varphi^*\bar k(E_2)$; the inclusion of function fields is induced by a morphism $\lambda\colon E_2\to E_3$, which sends origin to origin. Uniqueness holds because $\varphi$ is surjective. For the field of definition, $\sigma(\lambda)\circ\varphi=\sigma(\psi)=\psi$ for $\sigma\in\operatorname{Gal}(\bar k/k)$, so $\sigma(\lambda)=\lambda$. A good expansion adds pages for the Galois property of a separable isogeny's function-field extension and for the equivalence between curves and their function fields.

The extended Chapter 9 of Galbraith prints the separability hypothesis on $\psi$; the author's errata correct it to $\varphi$, as here and as in Silverman, Corollary III.4.11, which Charles, Goren and Lauter quote.

## Sources

- Steven D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press (2012); extended and corrected version 2.0 of Chapter 9, [author's copy](https://www.math.auckland.ac.nz/~sgal018/crypto-book/ch9.pdf) (numbering of the extended version), Theorem 9.6.18.
- Steven D. Galbraith, [errata to *Mathematics of Public Key Cryptography*](https://www.math.auckland.ac.nz/~sgal018/crypto-book/crypto-book.html), entry for Section 9.6, Theorem 9.6.18.
- Denis X. Charles, Eyal Z. Goren, Kristin E. Lauter, "Cryptographic Hash Functions from Expander Graphs", *Journal of Cryptology* 22 (2009) 93–113, [doi:10.1007/s00145-007-9002-x](https://doi.org/10.1007/s00145-007-9002-x), Section 5.2.1.
