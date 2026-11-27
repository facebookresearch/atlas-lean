# Derivative of the signature in its lower endpoint

Let every component of the velocity of $X$ be continuous. Then for every real $b$, letter $i$ and
word $w$, the map $c \mapsto S(X)^{i\,w}_{c,b}$ is differentiable with

$$\frac{d}{dc}\, S(X)^{i\,w}_{c,b} = -\,v^i(c)\, S(X)^{w}_{c,b},$$

and $c \mapsto S(X)^{\varnothing}_{c,b} = 1$ is constant. The proof differentiates
[Chen's identity](signature-chen.md) $S_{c_0,b} = S_{c_0,c} \otimes S_{c,b}$ at $c = c_0$, by
induction on the length of the word, using the derivative in the upper endpoint
([the signature solves $dS = S \otimes dX$](has-deriv-at-signature-concat.md)).
