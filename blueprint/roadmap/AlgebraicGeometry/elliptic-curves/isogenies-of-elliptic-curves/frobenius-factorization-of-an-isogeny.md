# In positive characteristic, every nonzero isogeny is a separable isogeny after a power of Frobenius

In characteristic $p>0$, a nonzero isogeny factors as a power of the $p$-power Frobenius followed by a separable isogeny. The exponent and the separable factor give its inseparable and separable degrees.

Let $k$ be a field of characteristic $p>0$ and let $\alpha\colon E_1\to E_2$ be a nonzero [isogeny](isogeny-of-elliptic-curves.md) of elliptic curves over $k$. For $n\ge 0$ let $E_1^{(p^n)}$ be the elliptic curve whose Weierstrass coefficients are those of $E_1$ raised to the power $p^n$, and let $\pi^n\colon E_1\to E_1^{(p^n)}$ be the morphism $(x:y:z)\mapsto(x^{p^n}:y^{p^n}:z^{p^n})$. Then there are an integer $n\ge 0$ and a separable isogeny $\alpha_{\mathrm{sep}}\colon E_1^{(p^n)}\to E_2$ with

$$
\alpha=\alpha_{\mathrm{sep}}\circ\pi^n,\qquad \deg\alpha=p^n\,\deg\alpha_{\mathrm{sep}}.
$$

The integer $n$ is determined by $\alpha$. The *separable degree* and *inseparable degree* of $\alpha$ are $\deg_s\alpha=\deg\alpha_{\mathrm{sep}}$ and $\deg_i\alpha=p^n$, so that $\deg\alpha=\deg_s\alpha\,\deg_i\alpha$. The isogeny $\alpha$ is separable exactly when $n=0$, and purely inseparable exactly when $\deg_s\alpha=1$. In characteristic $0$ every nonzero isogeny is separable, and one sets $\deg_s\alpha=\deg\alpha$ and $\deg_i\alpha=1$.

The curve $E_1^{(p^n)}$ need not be $E_1$; it is $E_1$ when $E_1$ is defined over the field with $p^n$ elements.

## Depends on

- [Isogeny of elliptic curves](isogeny-of-elliptic-curves.md)

## Proof depends on

None.

## Expansion

Sutherland states this corollary for isogenies over any field of characteristic $p>0$ and proves it for curves $y^2=f(x)$ with $p>3$. There an inseparable isogeny has the form $\alpha(x,y)=\bigl(r_1(x^p),\,r_2(x^p)\,y^p\bigr)$ with $r_1,r_2\in k(x)$ (his Lemma 5.3), so $\alpha=\alpha_1\circ\pi$ with $\alpha_1=(r_1(x),r_2(x)y)$ of degree $\deg\alpha/p$, and induction on the degree gives the factorization and the degree formula. In field terms, $\pi^n$ identifies $\bar k(E_1^{(p^n)})$ with an intermediate field $L$ of $\bar k(E_1)\supseteq L\supseteq\alpha^*\bar k(E_2)$; the extension $\bar k(E_1)/L$ is purely inseparable of degree $p^n$ and $L/\alpha^*\bar k(E_2)$ is separable, of degree $\deg\alpha_{\mathrm{sep}}$. Galbraith states the factorization for curves over $\bar{\mathbb{F}}_p$ (his Theorem 9.6.17) and refers to Silverman for the proof. The exponent is unique: if $\beta\circ\pi^n=\gamma\circ\pi^m$ with $\beta,\gamma$ separable and $n<m$, cancelling the surjective map $\pi^n$ gives $\beta=\gamma\circ\pi^{m-n}$, which is inseparable. A good expansion adds a page for the factorization of a morphism of curves through the relative Frobenius in general, which the proof beyond $y^2=f(x)$, $p>3$, needs.

## Sources

- Andrew V. Sutherland, *18.783 Elliptic Curves*, MIT lecture notes, Spring 2021, [Lecture 5: Isogeny kernels and division polynomials](https://math.mit.edu/classes/18.783/2021/LectureNotes5.pdf), Lemma 5.3, Corollary 5.4, Remark 5.5 and Definition 5.6.
- Steven D. Galbraith, *Mathematics of Public Key Cryptography*, Cambridge University Press (2012); extended and corrected version 2.0 of Chapter 9, [author's copy](https://www.math.auckland.ac.nz/~sgal018/crypto-book/ch9.pdf) (numbering of the extended version), Theorem 9.6.17 (curves over $\bar{\mathbb{F}}_p$).
- Luca De Feo, "Mathematics of Isogeny Based Cryptography", lecture notes, arXiv:1711.04062v1 (2017), Definition 24, item 5.
