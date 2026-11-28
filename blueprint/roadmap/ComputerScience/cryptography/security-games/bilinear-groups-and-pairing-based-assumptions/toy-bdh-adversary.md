# Discrete-logarithm adversary for the toy BDH game

For every natural number $q$, the construction takes $x, y, z \in \mathbb{Z}/q\mathbb{Z}$ and outputs the point mass at the product $xyz$. For $q > 1$ it is an adversary on the [toy exponent model](toy-model.md) of order $q$, whose three inputs come from $G_1$, $G_1$ and $G_2$. In the toy model group elements are their own exponents, so this adversary computes the answer of the bilinear Diffie–Hellman game directly.
