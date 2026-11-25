# Free variables are uncorrelated

In a noncommutative probability space ($\varphi(1) = 1$), if $(B_k)$ is
[freely independent](is-freely-independent.md), $i \ne j$, $a \in B_i$ and $b \in B_j$, then

$$\varphi(ab) = \varphi(a)\,\varphi(b).$$

Proof: the centred elements $a - \varphi(a)1 \in B_i$ and $b - \varphi(b)1 \in B_j$ form an
alternating word of length two, so $\varphi\bigl((a - \varphi(a))(b - \varphi(b))\bigr) = 0$; expanding
gives the identity. Longer alternating words give the genuinely free relations, for instance
$\varphi(abab) = \varphi(a^2)\varphi(b)^2 + \varphi(a)^2\varphi(b^2) - \varphi(a)^2\varphi(b)^2$.

## Sources

- G. W. Anderson, A. Guionnet and O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press, 2010 (numbering of the authors' pre-publication manuscript (2009), https://www.math.nyu.edu/~zeitouni/cupbook.pdf), Definition 5.3.1 and Remark 5.3.2.
