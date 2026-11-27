# Perimeter-to-area bound on seed loss from a habitat patch

**Setting.** A plant population is spread uniformly over a habitat patch $H\subset\mathbb R^2$ of finite area $A$ and perimeter $L$. Each seed is displaced from its parent at $x'$ by a random vector $X_d$ with density $f_d$, independent of $x'$, and has mean dispersal distance $\mu=\mathbb E|X_d|<\infty$. The *seed loss probability* is the chance that a random seed lands outside $H$:

$$p=\frac1A\iint_{x'\in H}\iint_{x\in H^c} f_d(x-x')\,dA\,dA .$$

**Theorem.**

$$p\le\frac{\mu L}{2A}.$$

If, in addition, the dispersal kernel is rotationally symmetric, $f_d(r,\theta)=\hat f_d(r)$, then

$$p\le\frac{\mu L}{\pi A}.$$

## Proof sketch

The proof turns seed loss into a boundary flux. In polar coordinates $x=(r_x,\theta_x)$ define the radial vector field $F(x)=\dfrac{x}{r_x^2}\displaystyle\int_{r_x}^\infty f_d(r,\theta_x)\,r\,dr$, whose flux across an arc equals the probability that a seed travelling in a straight line from the origin crosses that arc. Then $\nabla\cdot F=-f_d$ away from $0$, and for a plant at $x'$ the divergence theorem gives

$$\iint_{H^c}f_d(x-x')\,dA=\oint_{\partial H}F(x-x')\cdot n\,ds.$$

Averaging over $x'\in H$ and exchanging the integrals, $p=\frac1A\oint_{\partial H}G(x)\cdot n\,ds$ with $G(x)=\iint_H F(x-x')\,dA'$. A pointwise bound $G\cdot n\le \tfrac12(n\cdot\mathbb E X_d)+\tfrac\mu2\le\mu/2$, improved to $\mu/\pi$ by averaging over directions in the isotropic case, integrated over the boundary gives the result. The bounds depend on the patch only through $L/A$, so fragmented or elongated patches lose more seeds. Fat-tailed kernels with the same mean are covered as well.

## Sources

- Benjamin Hafner and Katherine Meyer, "Bounding Seed Loss from Isolated Habitat Patches", *Bulletin of Mathematical Biology* 86 (2024), 141, <https://doi.org/10.1007/s11538-024-01367-0>. Preprint version: arXiv:2404.09947 (2024), Proposition 1 (double-integral form of $p$), Lemma 2 (divergence identity), Proposition 4 (flux form), Lemmas 5–6 (pointwise bounds), Theorem 7 (main bounds), appendix "Sharpness of bounds", <https://doi.org/10.48550/arXiv.2404.09947>.
