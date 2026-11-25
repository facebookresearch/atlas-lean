# Hodge–Riemann relations for matroids

Let $M$ be a finite loopless matroid of rank $r + 1$, $\deg$ its degree map, and
$\ell = \ell(c)$ the class of a strictly submodular function $c$. For every integer $q$
with $2q \le r$, the symmetric bilinear form

$$Q_\ell^q(a_1, a_2) = (-1)^q \deg(a_1 \, \ell^{r-2q} \, a_2)$$

on $A^q(M)_\mathbb{R}$ is positive definite on the kernel of multiplication by
$\ell^{r-2q+1}$: if $a \in A^q(M)_\mathbb{R}$ is nonzero and $\ell^{r-2q+1} a = 0$,
then $(-1)^q \deg(a \, \ell^{r-2q} a) > 0$.

This is part (2) of the main theorem of Adiprasito, Huh and Katz. Suppose $r \ge 2$. The hard
Lefschetz theorem gives the decomposition
$A^1(M)_\mathbb{R} = \langle \ell \rangle \oplus P^1_\ell$ with
$P^1_\ell = \ker(\ell^{r-1})$, orthogonal for the form
$(a_1, a_2) \mapsto \deg(a_1 \ell^{r-2} a_2)$. The relation in degree $0$ makes this form
positive on $\ell$ ($\deg \ell^r > 0$), and the relation in degree $1$ makes it negative
definite on $P^1_\ell$. Together they say that the form has exactly one positive eigenvalue on
$A^1(M)_\mathbb{R}$ (this is the argument in the proof of AHK Lemma 9.6). A limiting argument
for nef classes then gives the inequality
$\deg(\ell_1^2 \ell_2^{r-2}) \deg(\ell_2^r) \le \deg(\ell_1 \ell_2^{r-1})^2$
(AHK Lemma 9.6), the source of the log-concavity of characteristic polynomials. Huh's ICM survey
explains this "one positive eigenvalue" consequence of the Hodge–Riemann relations as the common
mechanism behind many log-concavity results.

## Sources

- K. Adiprasito, J. Huh and E. Katz, *Hodge theory for combinatorial geometries*, Ann. of
  Math. 188 (2018), 381–452, Theorem 1.4 (2), Theorem 8.8 and Lemma 9.6, https://arxiv.org/abs/1511.02888.
- J. Huh, *Combinatorial applications of the Hodge–Riemann relations*, Proceedings of the ICM
  2018, Vol. 3, 3079–3098, Section 1, https://arxiv.org/abs/1711.11176.
