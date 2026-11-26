# Discrete-logarithm adversary for the toy BDH game

For an integer $q$, the adversary on the [toy exponent model](toy-model.md) of order $q$ takes $x, y, z \in \mathbb{Z}/q\mathbb{Z}$, the elements of the three groups of that model, and outputs the point mass at the product $xyz$. In the toy model group elements are their own exponents, so this adversary computes the answer of the bilinear Diffie–Hellman game directly.
