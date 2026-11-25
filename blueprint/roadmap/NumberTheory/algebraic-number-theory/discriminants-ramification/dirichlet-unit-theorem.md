# Dirichlet's unit theorem: the logarithmic image of the units is a full lattice

Let $K$ be a number field, $U_K$ the unit group of its ring of integers and $S_\infty$ its set of infinite
places, and fix $w_0 \in S_\infty$. For $w \in S_\infty$ let $\|\cdot\|_w$ be the absolute value at $w$
($\|x\|_w = |\varphi(x)|$ for an embedding $\varphi \colon K \to \mathbb{C}$ inducing $w$), and let $m_w$ be $1$
if $w$ is real and $2$ if $w$ is complex. Then the image of $U_K$ under the homomorphism

$$U_K \to \mathbb{R}^{S_\infty \setminus \{w_0\}}, \qquad u \mapsto (m_w \log \|u\|_w)_{w \ne w_0},$$

is a full lattice in $\mathbb{R}^{S_\infty \setminus \{w_0\}}$: a discrete subgroup that spans
$\mathbb{R}^{S_\infty \setminus \{w_0\}}$ over $\mathbb{R}$.

The numbers $m_w \log \|u\|_w$ are the logarithms of the normalized absolute values of $u$, and their sum
over all of $S_\infty$ is $\log |\mathrm{Nm}_{K/\mathbb{Q}}(u)| = 0$. So the map
$\lambda \colon u \mapsto (m_w \log \|u\|_w)_{w \in S_\infty}$ takes values in the hyperplane
$H = \{ x \in \mathbb{R}^{S_\infty} : \sum_w x_w = 0 \}$, and leaving out the coordinate of $w_0$ is a linear
isomorphism of $H$ onto $\mathbb{R}^{S_\infty \setminus \{w_0\}}$, with inverse
$x \mapsto (x, -\sum_{w \ne w_0} x_w)$. The statement is therefore equivalent to: $\lambda(U_K)$ is a full
lattice in $H$, of dimension $r + s - 1$ if $K$ has $r$ real and $s$ complex places. Milne proves it in this
form, with the usual absolute values, $L(\alpha) = (\log |\sigma_1 \alpha|, \dots, \log |\sigma_{r+s} \alpha|)$,
and the hyperplane $x_1 + \dots + x_r + 2x_{r+1} + \dots + 2x_{r+s} = 0$; doubling the coordinates of the
complex places carries his form to this one. The kernel of $\lambda$ is the finite group $\mu(K)$ of roots
of unity in $K$, so that $U_K \cong \mu(K) \times \mathbb{Z}^{r+s-1}$ (Milne, Proposition 5.8 and Theorem 5.1).
In Milne's proof, the lattice is discrete because only finitely many algebraic integers of bounded degree
have all their conjugates bounded, and it spans because units small at all infinite places but one
generate a subgroup of finite index (Theorem 5.9, with Lemma 5.10).

## Sources

- J. S. Milne, *Algebraic Number Theory*, version 3.08 (2020),
  <https://www.jmilne.org/math/CourseNotes/ANT.pdf>, Chapter 5: Theorem 5.1 (the unit theorem: finitely
  generated of rank $r + s - 1$, with torsion $\mu(K)$), the definition of $L$ and $H$ before Proposition
  5.8 ("Dropping the last coordinate defines an isomorphism $H \approx \mathbb{R}^{r+s-1}$"), Proposition
  5.8 and Theorem 5.9 (the image is a full lattice in $H$), with their proofs and Lemma 5.10.
