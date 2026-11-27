# Fréchet distance of curves

A *curve* in $\mathbb{R}^d$ is a continuous map $\pi : [0, 1] \to \mathbb{R}^d$; it is *polygonal* if it is a concatenation of finitely many segments, each traversed at constant speed. A *reparameterization* is a continuous bijection $f : [0, 1] \to [0, 1]$ with $f(0) = 0$ and $f(1) = 1$. The *Fréchet distance* between curves $\pi$ and $\sigma$ is

$$d_F(\pi, \sigma) = \inf_{f, g} \max_{t \in [0,1]} \|\pi(f(t)) - \sigma(g(t))\|,$$

the infimum over pairs of reparameterizations $f, g$.

## Sources

- S. Har-Peled, *Geometric Approximation Algorithms*, revised online chapter "Fréchet distance: How to walk your dog" (Chapter 33), <https://sarielhp.org/book/chapters/frechet.pdf>: Section 33.1.3 and Definition 33.1.6 (reparameterizations, leash length $h_{\pi,\sigma}(f, g)$ and the Fréchet distance)
