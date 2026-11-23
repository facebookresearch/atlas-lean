# Generalized von Neumann theorem, general form

Let $G$ be a finite abelian group, let $\mathbb{E}$ denote an average over $G$, let  $m \ge 2$, let $a_0, \dots, a_{m-1}$ be integers whose pairwise differences are coprime to $|G|$, and let $f_0, \dots, f_{m-1} : G \to \mathbb{C}$ take values in the closed unit disc. Then for every $j_0$,

$$\Bigl|\mathbb{E}_{x, h \in G} \prod_{j < m} f_j(x + a_j h)\Bigr| \le \|f_{j_0}\|_{U^{m-1}}.$$

This is statement (4.2) in Green and Tao's proof of their Proposition 1.7. Their proof is by induction on $m$: after the change of variables $x \mapsto x + a_{j_1} h$ for some $j_1 \ne j_0$, the van der Corput inequality (4.1) removes $f_{j_1}$ and replaces the other functions by multiplicative derivatives, the induction hypothesis applies to the shifted coefficients $a_j - a_{j_1}$, and Hölder's inequality with the substitution $h = (a_{j_0} - a_{j_1}) k$, which is a bijection of $G$ because $a_{j_0} - a_{j_1}$ is coprime to $|G|$, and the recursion (1.1) finish. The induction starts at $m = 2$, where the bound is $|\mathbb{E} f_0|\,|\mathbb{E} f_1| \le |\mathbb{E} f_{j_0}|$.

## Informally uses

- [Gowers uniformity norm, raised to the power $2^d$](gowers-pow.md): the recursion (1.1), used in the last step.
- [Multiplicative derivative](mul-deriv.md): the functions $T^{(a_j - a_{j_1}) k} f_j \overline{f_j}$ produced by the van der Corput inequality, with the shifted coefficients.

## Sources

- B. Green and T. Tao, "An inverse theorem for the Gowers $U^3(G)$ norm", Proc. Edinb. Math. Soc. 51 (2008), 73–153; numbering of arXiv:math/0503014, proof of Proposition 1.7, (4.1) and (4.2).
