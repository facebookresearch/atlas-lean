# Gödel numbers of finite tuples

A tuple $(x_0, \dots, x_{l-1}) \in \mathbb{N}^l$ is coded recursively by

$$\mathrm{code}() = 0, \qquad \mathrm{code}(x_0, \dots, x_l) = \langle \mathrm{code}(x_0, \dots, x_{l-1}),\, x_l \rangle.$$

Here $\langle a, b \rangle$ is the pairing function on $\mathbb{N}$ given by $\langle a, b \rangle = b^2 + a$ if $a < b$ and $\langle a, b \rangle = a^2 + a + b$ otherwise; it is a bijection $\mathbb{N}^2 \to \mathbb{N}$.
